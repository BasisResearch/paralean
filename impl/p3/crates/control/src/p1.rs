//! Reading impl/p1 stores: group bytes (`objects/<declId>.grp`) and group metadata
//! (`meta/<gid>.json`, P1's `GroupRec`). In the P2 store a P1 group is published as the
//! group payload (its `.grp` bytes, so P2's group ID is P1's `declId`) with its metadata
//! JSON as the capsule. The validator rebuilds a P1 store from those two objects of the group
//! and of each dependency.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use paralean_store::{Domain, Id, Kind, Name, NameComp, Opaque};
use serde_json::Value;

/// One P1 group: its package ID (`gid`), its group ID and both payloads.
#[derive(Clone, Debug)]
pub struct P1Group {
    pub gid: String,
    pub decl: Id,
    pub meta_json: Vec<u8>,
    pub meta: Value,
    pub grp: Vec<u8>,
}

impl P1Group {
    /// Parse metadata JSON and pair it with group bytes; the bytes must hash to `declId`.
    pub fn from_parts(meta_json: Vec<u8>, grp: Vec<u8>) -> Result<P1Group, String> {
        let meta: Value = serde_json::from_slice(&meta_json).map_err(|e| format!("metadata: {e}"))?;
        let gid = meta["gid"].as_str().ok_or("metadata has no gid")?.to_string();
        let decl = Id::from_hex(meta["declId"].as_str().ok_or("metadata has no declId")?).ok_or("bad declId")?;
        if Domain::Group.hash(&grp) != decl {
            return Err(format!("group bytes do not hash to declId {}", decl.hex()));
        }
        Ok(P1Group { gid, decl, meta_json, meta, grp })
    }

    pub fn group_object(&self) -> Opaque {
        Opaque::new(Kind::Group, self.grp.clone())
    }
    pub fn capsule_object(&self) -> Opaque {
        Opaque::new(Kind::Capsule, self.meta_json.clone())
    }
    pub fn capsule_id(&self) -> Id {
        self.capsule_object().id()
    }
    /// Package IDs of kernel and frontend dependencies.
    pub fn deps(&self) -> Vec<String> {
        let mut v = Vec::new();
        for k in ["deps", "feDeps"] {
            for d in self.meta[k].as_array().into_iter().flatten() {
                if let Some(s) = d.as_str() {
                    v.push(s.to_string());
                }
            }
        }
        v
    }
    /// Names this group publishes revisions for: its public names, else its anchor.
    pub fn names(&self) -> Vec<Name> {
        let mut v: Vec<Name> = self.meta["publicNames"].as_array().into_iter().flatten().filter_map(name_of).collect();
        if v.is_empty() {
            v.extend(name_of(&self.meta["anchor"]));
        }
        v.sort();
        v.dedup();
        v
    }
    /// The statement hash capture recorded for member `n` (P1 `typeHash`).
    pub fn statement(&self, n: &Name) -> Option<String> {
        self.meta["members"].as_array()?.iter().find(|m| name_of(&m["name"]).as_ref() == Some(n))?["typeHash"]
            .as_str()
            .map(str::to_string)
    }
    pub fn file(&self) -> String {
        self.meta["capsule"]["file"].as_str().unwrap_or("").to_string()
    }
}

/// A Lean name in P1's JSON form (array of string or number components).
pub fn name_of(v: &Value) -> Option<Name> {
    let a = v.as_array()?;
    if a.is_empty() {
        return None;
    }
    Some(Name(
        a.iter()
            .map(|c| match c {
                Value::String(s) => Some(NameComp::Str(s.clone())),
                Value::Number(n) => n.as_u64().map(|n| NameComp::Num(n as u128)),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?,
    ))
}

/// All publishable groups of a P1 store, by package ID.
pub fn load_store(root: &Path) -> Result<BTreeMap<String, P1Group>, String> {
    let mut out = BTreeMap::new();
    let dir = root.join("meta");
    for e in std::fs::read_dir(&dir).map_err(|e| format!("{}: {e}", dir.display()))? {
        let p = e.map_err(|e| e.to_string())?.path();
        if p.extension().and_then(|x| x.to_str()) != Some("json") {
            continue;
        }
        let meta_json = std::fs::read(&p).map_err(|e| e.to_string())?;
        let meta: Value = serde_json::from_slice(&meta_json).map_err(|e| format!("{}: {e}", p.display()))?;
        let decl = meta["declId"].as_str().ok_or("no declId")?;
        let grp = std::fs::read(root.join("objects").join(format!("{decl}.grp"))).map_err(|e| e.to_string())?;
        let g = P1Group::from_parts(meta_json, grp)?;
        out.insert(g.gid.clone(), g);
    }
    Ok(out)
}

/// The dependency closure of `gid` in dependency order (dependencies first, `gid` last).
pub fn closure(groups: &BTreeMap<String, P1Group>, gid: &str) -> Result<Vec<String>, String> {
    let mut order = Vec::new();
    let mut done = BTreeSet::new();
    let mut stack = vec![(gid.to_string(), false)];
    while let Some((g, post)) = stack.pop() {
        if post {
            if done.insert(g.clone()) {
                order.push(g);
            }
            continue;
        }
        if done.contains(&g) {
            continue;
        }
        let m = groups.get(&g).ok_or_else(|| format!("closure: missing group {g}"))?;
        stack.push((g.clone(), true));
        for d in m.deps().into_iter().rev() {
            if !done.contains(&d) {
                stack.push((d, false));
            }
        }
    }
    Ok(order)
}

/// Write a P1 store holding exactly `groups` (the validator's per-job input).
pub fn write_store(root: &Path, groups: &[P1Group]) -> std::io::Result<PathBuf> {
    std::fs::create_dir_all(root.join("objects"))?;
    std::fs::create_dir_all(root.join("meta"))?;
    std::fs::create_dir_all(root.join("files"))?;
    for g in groups {
        std::fs::write(root.join("objects").join(format!("{}.grp", g.decl.hex())), &g.grp)?;
        std::fs::write(root.join("meta").join(format!("{}.json", g.gid)), &g.meta_json)?;
    }
    Ok(root.to_path_buf())
}
