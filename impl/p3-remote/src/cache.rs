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

use paralean_store::{Anchor, Id, Marker, Name, NameComp, Revision, Tombstone};
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
    pub fn put_capsule(&self, c: &Id, bytes: &[u8]) -> Result<String, String> {
        let v: Value = serde_json::from_slice(bytes).map_err(|e| format!("capsule {c}: {e}"))?;
        let pid = v.get("gid").and_then(|x| x.as_str()).ok_or("capsule without gid")?.to_string();
        self.write_new(&self.capsule(c), bytes).map_err(|e| e.to_string())?;
        self.write_new(&self.meta(&pid), bytes).map_err(|e| e.to_string())?;
        Ok(pid)
    }

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
