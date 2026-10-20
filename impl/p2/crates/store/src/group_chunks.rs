//! Explicit chunk references for newly encoded groups. Legacy P1 group bytes keep their ID
//! and remain opaque; no sidecar is trusted to assert a complete chunk list for them.

use std::collections::BTreeMap;

use crate::error::{Result, StoreError};
use crate::id::{Id, Kind};
use crate::objects::Opaque;
use crate::pce::{Dec, Enc, Pce};

pub const MAGIC: &str = "paralean-group-chunked-v1";
pub const MAX_REFS: usize = 4096;
pub const MAX_CHUNK_BYTES: u64 = 64 * 1024 * 1024;

/// Logical order is retained in the group ID; a repeated ID must declare the same length.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChunkRef { pub id: Id, pub length: u64 }

/// Build an opaque group under the existing `v0/group` hash domain. `core` is consumed by
/// the producer and checker; P2 only validates the envelope and transfers the named chunks.
pub fn chunked_group(core: &[u8], chunks: &[ChunkRef]) -> Result<Opaque> {
    if core.is_empty() || chunks.len() > MAX_REFS { return Err(StoreError::Invalid("invalid chunked group core or reference count".into())); }
    let mut e = Enc::new();
    e.raw(MAGIC.as_bytes()).uvarint(1).bytes(core);
    e.list(chunks, |e, c| { c.id.encode(e); e.uvarint(c.length); });
    let group = Opaque::new(Kind::Group, e.finish());
    let _ = parse_group_chunks(&group.pce)?;
    Ok(group)
}

/// `None` means legacy/unknown opaque bytes: chunk completeness is unknown, not zero.
pub fn parse_group_chunks(group_pce: &[u8]) -> Result<Option<Vec<ChunkRef>>> {
    if !group_pce.starts_with(MAGIC.as_bytes()) {
        if (group_pce.len() >= 8 && MAGIC.as_bytes().starts_with(group_pce))
            || group_pce.starts_with(b"paralean-group-chunked") {
            return Err(StoreError::Invalid("malformed or unsupported chunked group encoding".into()));
        }
        return Ok(None);
    }
    let mut d = Dec::new(&group_pce[MAGIC.len()..]);
    if d.uvarint()? != 1 { return Err(StoreError::Invalid("unsupported chunked group version".into())); }
    if d.bytes()?.is_empty() { return Err(StoreError::Invalid("empty chunked group core".into())); }
    let count = d.uvarint()?;
    if count > MAX_REFS as u64 { return Err(StoreError::Invalid("too many group chunk references".into())); }
    let mut refs = Vec::with_capacity(count as usize);
    for _ in 0..count { refs.push(ChunkRef { id: Id::decode(&mut d)?, length: d.uvarint()? }); }
    d.end()?;
    let mut lengths = BTreeMap::new();
    for r in &refs {
        if !(1..=MAX_CHUNK_BYTES).contains(&r.length) { return Err(StoreError::Invalid("invalid group chunk length".into())); }
        if lengths.insert(r.id, r.length).is_some_and(|old| old != r.length) {
            return Err(StoreError::Invalid("one chunk ID has two lengths".into()));
        }
    }
    Ok(Some(refs))
}

pub fn unique_chunks(group_pce: &[u8]) -> Result<Option<BTreeMap<Id, u64>>> {
    Ok(parse_group_chunks(group_pce)?.map(|refs| refs.into_iter().map(|r| (r.id, r.length)).collect()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn legacy_opaque_group_has_unknown_chunk_coverage() {
        assert_eq!(parse_group_chunks(b"opaque P1 group bytes").unwrap(), None);
        assert_eq!(parse_group_chunks(b"").unwrap(), None);
    }

    #[test]
    fn valid_wrapper_preserves_order_and_deduplicates_transfer_refs() {
        let a = Id([1; 32]);
        let b = Id([2; 32]);
        let refs = vec![ChunkRef { id: b, length: 11 }, ChunkRef { id: a, length: 7 }, ChunkRef { id: b, length: 11 }];
        let group = chunked_group(b"opaque core", &refs).unwrap();
        assert_eq!(parse_group_chunks(&group.pce).unwrap(), Some(refs));
        assert_eq!(unique_chunks(&group.pce).unwrap(), Some(BTreeMap::from([(a, 7), (b, 11)])));
    }

    #[test]
    fn reserved_prefix_is_fail_closed() {
        assert!(parse_group_chunks(&MAGIC.as_bytes()[..12]).is_err());
        assert!(parse_group_chunks(b"paralean-group-chunked-v2\0").is_err());
        let group = chunked_group(b"core", &[ChunkRef { id: Id([3; 32]), length: 1 }]).unwrap();
        for n in [MAGIC.len(), MAGIC.len() + 1, group.pce.len() - 1] {
            assert!(parse_group_chunks(&group.pce[..n]).is_err());
        }
        let mut trailing = group.pce.clone();
        trailing.push(0);
        assert!(parse_group_chunks(&trailing).is_err());
    }

    #[test]
    fn conflicting_lengths_and_unbounded_refs_are_rejected() {
        let id = Id([4; 32]);
        assert!(chunked_group(b"core", &[ChunkRef { id, length: 1 }, ChunkRef { id, length: 2 }]).is_err());
        assert!(chunked_group(b"core", &[ChunkRef { id, length: MAX_CHUNK_BYTES + 1 }]).is_err());
        let refs = vec![ChunkRef { id, length: 1 }; MAX_REFS + 1];
        assert!(chunked_group(b"core", &refs).is_err());
    }
}
