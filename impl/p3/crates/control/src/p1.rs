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
        // The gid names a file in the validator's scratch store and an entry of the
        // checker's comma-separated `--gids`: it must be a P1 package ID, nothing else.
        check_gid(&gid)?;
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

/// A P1 package ID: `H("v0/package", …)` as 64 lowercase hex digits. Anything else
/// (`../x`, an absolute path, `a,b`) could escape the scratch store or add `--gids`
/// entries, so it is refused before any file is written. (The ID is not recomputed here:
/// that needs Lean's exact JSON rendering of the capsule; the checker re-derives it.)
pub fn check_gid(gid: &str) -> Result<(), String> {
    if cfg!(feature = "mutate-unchecked-gid") {
        return Ok(());
    }
    if gid.len() == 64 && gid.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)) {
        Ok(())
    } else {
        Err(format!("metadata gid {:?} is not a package ID (64 lowercase hex digits)", gid.chars().take(80).collect::<String>()))
    }
}

/// Write a P1 store holding exactly `groups` (the validator's per-job input). `root` must
/// not exist: it is created private (0700) and every file is created new, so nothing
/// outside it is written and nothing already there is followed or overwritten. Package
/// IDs must be well formed and distinct.
pub fn write_store(root: &Path, groups: &[P1Group]) -> std::io::Result<PathBuf> {
    use std::io::Write;
    use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
    let invalid = |m: String| std::io::Error::new(std::io::ErrorKind::InvalidInput, m);
    let mut gids = BTreeSet::new();
    for g in groups {
        check_gid(&g.gid).map_err(invalid)?;
        if !gids.insert(g.gid.as_str()) {
            return Err(invalid(format!("duplicate package ID {}", g.gid)));
        }
    }
    let mut dirs = std::fs::DirBuilder::new();
    dirs.mode(0o700);
    dirs.create(root)?;
    for d in ["objects", "meta", "files"] {
        dirs.create(root.join(d))?;
    }
    let create = |path: PathBuf, bytes: &[u8]| -> std::io::Result<()> {
        let mut f = std::fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(path)?;
        f.write_all(bytes)
    };
    let mut decls = BTreeSet::new();
    for g in groups {
        // Group bytes are content-addressed (re-hashed in `from_parts`): one file per ID.
        if decls.insert(g.decl) {
            create(root.join("objects").join(format!("{}.grp", g.decl.hex())), &g.grp)?;
        }
        create(root.join("meta").join(format!("{}.json", g.gid)), &g.meta_json)?;
    }
    Ok(root.to_path_buf())
}

#[cfg(test)]
mod gid_tests {
    use super::*;

    const GRP: &[u8] = b"group bytes";

    fn meta(gid: &str) -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!({"gid": gid, "declId": Domain::Group.hash(GRP).hex()})).unwrap()
    }

    #[test]
    fn hostile_gid_cannot_escape_the_scratch_store() {
        let base = std::env::temp_dir().join(format!("p1-gid-test-{}-{}", std::process::id(), rand::random::<u64>()));
        std::fs::create_dir_all(&base).unwrap();
        let good = "ab".repeat(32);
        let comma = format!("{good},{good}");
        let upper = "AB".repeat(32);
        for bad in ["../../escaped", "/tmp/paralean-gid-test-escaped", comma.as_str(), upper.as_str(), &good[..63], ""] {
            assert!(P1Group::from_parts(meta(bad), GRP.to_vec()).is_err(), "from_parts accepted gid {bad:?}");
            // The writer refuses it too, even for a group not built by `from_parts`.
            let g = P1Group { gid: bad.into(), decl: Domain::Group.hash(GRP), meta_json: meta(bad), meta: serde_json::Value::Null, grp: GRP.to_vec() };
            let root = base.join("jobs").join(format!("job-{}", rand::random::<u64>()));
            std::fs::create_dir_all(root.parent().unwrap()).unwrap();
            assert!(write_store(&root, &[g]).is_err(), "write_store accepted gid {bad:?}");
        }
        assert!(!base.join("escaped.json").exists() && !Path::new("/tmp/paralean-gid-test-escaped.json").exists());
        // A package ID is written once; a duplicate or an existing root is refused.
        let g = P1Group::from_parts(meta(&good), GRP.to_vec()).unwrap();
        let root = base.join("job-ok");
        write_store(&root, std::slice::from_ref(&g)).unwrap();
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(std::fs::metadata(&root).unwrap().permissions().mode() & 0o777, 0o700);
        assert!(root.join("meta").join(format!("{good}.json")).is_file());
        assert!(write_store(&root, std::slice::from_ref(&g)).is_err(), "existing scratch root reused");
        assert!(write_store(&base.join("job-dup"), &[g.clone(), g]).is_err(), "duplicate gid accepted");
        let _ = std::fs::remove_dir_all(&base);
        let _ = std::fs::remove_file("/tmp/paralean-gid-test-escaped.json");
    }
}
