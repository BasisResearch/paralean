//! A working copy's local cache of the store (the P1 store layout plus `p3/`).
//!
//! ```text
//! objects/<group>.grp            group payloads (P1 bytes = PCE), fetched on demand
//! meta/<pid>.json                P1 GroupRec of each known package (from its capsule)
//! p3/capsules/<capsule>.json     capsule objects as stored (P1 GroupRec JSON)
//! p3/jobs/<job>.bin              controller-signed job envelopes the receipts answer
//! p3/records/m-<marker>.json     publication records (markers) delivered by `pull`
//! p3/records/t-<tombstone>.json  tombstones delivered by `pull`
//! p3/revisions/<rev>.json        revisions named by known markers
//! p3/receipts/<receipt>.bin      signed receipts as stored (Signed<ReceiptBody> bytes)
//! p3/transfer.jsonl              one line per transfer (kind, id, bytes, ms)
//! ```
//!
//! Every file is written to a temporary name and renamed, so a reader never sees a partial
//! record. Records are immutable: an existing file is never rewritten.

use std::path::{Path, PathBuf};

use paralean_store::{check_file_path, Anchor, Id, Kind, Marker, Name, NameComp, Opaque, Revision, Tombstone};
use serde_json::{json, Value};

pub struct Cache {
    pub root: PathBuf,
}

pub fn name_json(n: &Name) -> Value {
    Value::Array(
        n.0.iter()
            .map(|c| match c {
                NameComp::Str(s) => json!(s),
                NameComp::Num(k) => json!(*k as u64),
            })
            .collect(),
    )
}

pub fn name_of_json(v: &Value) -> Result<Name, String> {
    let arr = v.as_array().ok_or("name: expected an array")?;
    let mut out = Vec::new();
    for c in arr {
        match c {
            Value::String(s) => out.push(NameComp::Str(s.clone())),
            Value::Number(k) => out.push(NameComp::Num(k.as_u64().ok_or("name: bad number")? as u128)),
            _ => return Err("name: bad component".into()),
        }
    }
    Ok(Name(out))
}

pub fn id_of(v: &Value) -> Result<Id, String> {
    let s = v.as_str().ok_or("expected a hex ID")?;
    Id::from_hex(s).ok_or(format!("bad ID {s}"))
}

impl Cache {
    pub fn new(root: &str) -> Cache {
        Cache { root: PathBuf::from(root) }
    }
    pub fn p3(&self) -> PathBuf {
        self.root.join("p3")
    }
    pub fn init(&self) -> std::io::Result<()> {
        for d in ["objects", "meta", "files", "p3/capsules", "p3/records", "p3/fetched", "p3/revisions", "p3/receipts", "p3/jobs"] {
            std::fs::create_dir_all(self.root.join(d))?;
        }
        Ok(())
    }
    pub fn write_new(&self, p: &Path, bytes: &[u8]) -> std::io::Result<bool> {
        if p.exists() {
            return Ok(false);
        }
        if let Some(d) = p.parent() {
            std::fs::create_dir_all(d)?;
        }
        let tmp = p.with_extension(format!("tmp{}", std::process::id()));
        std::fs::write(&tmp, bytes)?;
        std::fs::rename(&tmp, p)?;
        Ok(true)
    }
    pub fn object(&self, g: &Id) -> PathBuf {
        self.root.join("objects").join(format!("{}.grp", g.hex()))
    }
    pub fn capsule(&self, c: &Id) -> PathBuf {
        self.p3().join("capsules").join(format!("{}.json", c.hex()))
    }
    pub fn tomb_rec(&self, t: &Id) -> PathBuf {
        self.p3().join("records").join(format!("t-{}.json", t.hex()))
    }
    pub fn revision(&self, r: &Id) -> PathBuf {
        self.p3().join("revisions").join(format!("{}.json", r.hex()))
    }
    pub fn receipt(&self, r: &Id) -> PathBuf {
        self.p3().join("receipts").join(format!("{}.bin", r.hex()))
    }
    pub fn job(&self, j: &Id) -> PathBuf {
        self.p3().join("jobs").join(format!("{}.bin", j.hex()))
    }
    pub fn meta(&self, pid: &str) -> PathBuf {
        self.root.join("meta").join(format!("{pid}.json"))
    }

    pub fn log_transfer(&self, kind: &str, id: &Id, bytes: usize, ms: f64) {
        use std::io::Write;
        let line = json!({"kind": kind, "id": id.hex(), "bytes": bytes, "ms": ms}).to_string();
        if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(self.p3().join("transfer.jsonl")) {
            let _ = writeln!(f, "{line}");
        }
    }

    /// Store a capsule (P1 group metadata JSON, as P3 control publishes it) and its copy
    /// under `meta/<pid>.json`; returns the pid.
    ///
    /// The pid is the capsule's self-declared `gid` (W2 A-8). It must be a 64-digit
    /// lowercase hex ID before it names a file, and the bytes must hash to the capsule ID.
    /// Lean recomputes the package ID from the contents on every read (`Store.getMeta`,
    /// `P3.loadCapsule`), so a capsule claiming another package's ID is refused there; here
    /// a different capsule already stored under the same pid is reported, never kept silently.
    pub fn put_capsule(&self, c: &Id, bytes: &[u8]) -> Result<String, String> {
        if !cfg!(feature = "mutate-unchecked-capsule-id") && Opaque::new(Kind::Capsule, bytes.to_vec()).id() != *c {
            return Err(format!("capsule {c}: bytes do not hash to the capsule ID"));
        }
        let v: Value = serde_json::from_slice(bytes).map_err(|e| format!("capsule {c}: {e}"))?;
        let pid = v.get("gid").and_then(|x| x.as_str()).ok_or("capsule without gid")?.to_string();
        if !cfg!(feature = "mutate-unchecked-pid") && !is_hex_id(&pid) {
            return Err(format!("capsule {c}: package ID {:?} is not a 64-digit lowercase hex ID", pid.chars().take(80).collect::<String>()));
        }
        self.write_new(&self.capsule(c), bytes).map_err(|e| e.to_string())?;
        let meta = self.meta(&pid);
        if !self.write_new(&meta, bytes).map_err(|e| e.to_string())? {
            let old = std::fs::read(&meta).map_err(|e| e.to_string())?;
            if old != bytes {
                return Err(format!("capsule {c}: another capsule is already stored for package {pid}"));
            }
        }
        Ok(pid)
    }

}

/// 64 lowercase hexadecimal digits (Lean `Safety.isHexId`).
pub fn is_hex_id(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// A marker record for the cache, after the decoder's field rules (W2 A-6): its file path
/// is where every syncing working copy writes.
pub fn checked_marker_json(mid: &Id, m: &Marker, capsule: &Id, pid: &str) -> Result<Value, String> {
    if !cfg!(feature = "mutate-unchecked-pid") && !is_hex_id(pid) {
        return Err(format!("marker {mid}: malformed package ID"));
    }
    m.check().map_err(|e| format!("marker {mid}: {e}"))?;
    Ok(marker_json(mid, m, capsule, pid))
}

/// A tombstone record for the cache, after the decoder's field rules.
pub fn checked_tomb_json(tid: &Id, t: &Tombstone) -> Result<Value, String> {
    check_file_path(&t.file_path).map_err(|e| format!("tombstone {tid}: {e}"))?;
    Ok(tomb_json(tid, t))
}

pub fn marker_json(mid: &Id, m: &Marker, capsule: &Id, pid: &str) -> Value {
    json!({
        "kind": "marker",
        "id": mid.hex(),
        "group": m.group.hex(),
        "revisions": m.revisions.iter().map(|r| r.hex()).collect::<Vec<_>>(),
        "receipt": m.receipt.hex(),
        "file": m.file_path,
        "anchor": match &m.anchor { Anchor::FileStart => Value::Null, Anchor::After(g) => json!(g.hex()) },
        "lamport": m.lamport,
        "author": m.author.hex(),
        "rootPath": m.root_path.iter().map(|(g, l, a)| json!([g.hex(), l, a.hex()])).collect::<Vec<_>>(),
        "lineageKeys": m.lineage_keys.iter().map(|(n, l, a)| json!([name_json(n), l, a.hex()])).collect::<Vec<_>>(),
        "capsule": capsule.hex(),
        "pid": pid,
    })
}

pub fn tomb_json(tid: &Id, t: &Tombstone) -> Value {
    json!({
        "kind": "tombstone",
        "id": tid.hex(),
        "file": t.file_path,
        "target": t.target.hex(),
        "position": t.position.map(|p| p.hex()),
        "lamport": t.lamport,
        "author": t.author.hex(),
    })
}

pub fn revision_json(rid: &Id, r: &Revision) -> Value {
    json!({
        "id": rid.hex(),
        "group": r.group.hex(),
        "name": name_json(&r.name),
        "parents": r.parents.iter().map(|p| p.hex()).collect::<Vec<_>>(),
        "capsule": r.capsule.hex(),
        "workspace": r.workspace.hex(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp(name: &str) -> Cache {
        let d = std::env::temp_dir().join(format!("plr-cache-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        let c = Cache { root: d };
        c.init().unwrap();
        c
    }

    fn capsule(gid: &str) -> (Id, Vec<u8>) {
        let bytes = serde_json::to_vec(&json!({"gid": gid, "declId": "00".repeat(32)})).unwrap();
        (Opaque::new(Kind::Capsule, bytes.clone()).id(), bytes)
    }

    #[test]
    fn put_capsule_refuses_traversing_package_ids_and_mismatched_bytes() {
        let c = temp("pid");
        let outside = c.root.join("pwned.json");
        for gid in ["../pwned", "../../pwned", "/tmp/pwned", "AB".repeat(32).as_str(), "", &"a".repeat(63)] {
            let (cid, bytes) = capsule(gid);
            assert!(c.put_capsule(&cid, &bytes).is_err(), "{gid:?} accepted");
        }
        assert!(!outside.exists(), "a package ID wrote outside meta/");
        assert!(std::fs::read_dir(c.root.join("meta")).unwrap().next().is_none());
        let (cid, bytes) = capsule(&"ab".repeat(32));
        let (other, _) = capsule(&"cd".repeat(32));
        assert!(c.put_capsule(&other, &bytes).is_err(), "bytes stored under another capsule ID");
        assert_eq!(c.put_capsule(&cid, &bytes).unwrap(), "ab".repeat(32));
        // A second, different capsule claiming the same package is reported, not hidden.
        let forged = serde_json::to_vec(&json!({"gid": "ab".repeat(32), "declId": "11".repeat(32)})).unwrap();
        let fid = Opaque::new(Kind::Capsule, forged.clone()).id();
        assert!(c.put_capsule(&fid, &forged).is_err());
        assert_eq!(std::fs::read(c.meta(&"ab".repeat(32))).unwrap(), bytes);
        let _ = std::fs::remove_dir_all(&c.root);
    }

    #[test]
    fn records_with_unsafe_file_paths_are_not_written() {
        let m = Marker {
            group: Id([1; 32]), revisions: vec![], receipt: Id([2; 32]), file_path: "../../.bashrc".into(),
            anchor: Anchor::FileStart, lamport: 1, author: paralean_store::AgentId([3; 16]),
            root_path: vec![], lineage_keys: vec![],
        };
        assert!(checked_marker_json(&Id([4; 32]), &m, &Id([5; 32]), &"ab".repeat(32)).is_err());
        let ok = Marker { file_path: "Test/File.lean".into(), ..m.clone() };
        assert!(checked_marker_json(&Id([4; 32]), &ok, &Id([5; 32]), &"ab".repeat(32)).is_ok());
        let t = Tombstone { file_path: ".git/config".into(), target: Id([1; 32]), lamport: 2, author: m.author, receipt: None, position: None };
        assert!(checked_tomb_json(&Id([6; 32]), &t).is_err());
    }
}
