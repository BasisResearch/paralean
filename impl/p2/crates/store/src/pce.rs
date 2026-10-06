//! Paralean canonical encoding (PCE), docs/p0-interfaces.md §1.1.
//!
//! - `uvarint`: unsigned LEB128, minimal length. Identical to P1's `W.nat` writer
//!   (impl/p1/Paralean/Encode.lean), which emits minimal LEB128 by construction.
//! - `bytes`: `uvarint len ‖ raw`; `string`: UTF-8 `bytes` (P1's `W.bytes`/`W.str`).
//! - `bool`: one byte `0x00`/`0x01` (P1's `W.bool`).
//! - `nat` (Lean `Nat`): `bytes` of the minimal big-endian magnitude; zero is empty.
//! - `option`: `0x00` or `0x01 ‖ value`. `list`: `uvarint count ‖ items`.
//!   `set`: a list sorted by the items' encoded bytes, duplicates rejected.
//! - `enum`: one tag byte, then the variant's fields.
//!
//! The decoder rejects trailing bytes, non-minimal varints, unsorted or duplicated sets,
//! non-minimal nats, bad booleans, invalid UTF-8 and unknown tags (a schema-valid decode).

use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum DecodeError {
    #[error("unexpected end of input")]
    Eof,
    #[error("non-minimal uvarint")]
    NonMinimalVarint,
    #[error("uvarint overflows u64")]
    VarintOverflow,
    #[error("non-minimal nat")]
    NonMinimalNat,
    #[error("invalid bool byte {0:#x}")]
    BadBool(u8),
    #[error("invalid UTF-8")]
    BadUtf8,
    #[error("unknown tag {tag} for {what}")]
    UnknownTag { what: &'static str, tag: u8 },
    #[error("set not sorted or has duplicates")]
    UnsortedSet,
    #[error("trailing bytes ({0})")]
    Trailing(usize),
    #[error("unsupported format {0}")]
    Format(u64),
    #[error("bad length for {what}: {len}")]
    BadLength { what: &'static str, len: usize },
    #[error("invalid field: {0}")]
    Invalid(&'static str),
}

pub type DResult<T> = Result<T, DecodeError>;

/// Byte writer.
#[derive(Default, Debug, Clone)]
pub struct Enc {
    pub out: Vec<u8>,
}

impl Enc {
    pub fn new() -> Self {
        Enc { out: Vec::new() }
    }
    pub fn byte(&mut self, b: u8) -> &mut Self {
        self.out.push(b);
        self
    }
    pub fn uvarint(&mut self, mut n: u64) -> &mut Self {
        loop {
            if n < 0x80 {
                self.out.push(n as u8);
                return self;
            }
            self.out.push((n as u8 & 0x7f) | 0x80);
            n >>= 7;
        }
    }
    pub fn bytes(&mut self, b: &[u8]) -> &mut Self {
        self.uvarint(b.len() as u64);
        self.out.extend_from_slice(b);
        self
    }
    pub fn raw(&mut self, b: &[u8]) -> &mut Self {
        self.out.extend_from_slice(b);
        self
    }
    pub fn string(&mut self, s: &str) -> &mut Self {
        self.bytes(s.as_bytes())
    }
    pub fn bool(&mut self, b: bool) -> &mut Self {
        self.byte(b as u8)
    }
    /// Lean `Nat` (here bounded by u128): minimal big-endian magnitude as `bytes`.
    pub fn nat(&mut self, n: u128) -> &mut Self {
        let be = n.to_be_bytes();
        let first = be.iter().position(|&b| b != 0).unwrap_or(be.len());
        self.bytes(&be[first..])
    }
    pub fn option<T>(&mut self, v: &Option<T>, f: impl FnOnce(&mut Enc, &T)) -> &mut Self {
        match v {
            None => {
                self.byte(0);
            }
            Some(x) => {
                self.byte(1);
                f(self, x);
            }
        }
        self
    }
    pub fn list<T>(&mut self, items: &[T], mut f: impl FnMut(&mut Enc, &T)) -> &mut Self {
        self.uvarint(items.len() as u64);
        for x in items {
            f(self, x);
        }
        self
    }
    /// A set: items encoded, sorted by their encodings, duplicates rejected (panics, since
    /// a writer that builds a set with duplicates has a bug; use `BTreeSet` upstream).
    pub fn set<T>(&mut self, items: &[T], mut f: impl FnMut(&mut Enc, &T)) -> &mut Self {
        let mut encs: Vec<Vec<u8>> = items
            .iter()
            .map(|x| {
                let mut e = Enc::new();
                f(&mut e, x);
                e.out
            })
            .collect();
        encs.sort();
        for w in encs.windows(2) {
            assert!(w[0] != w[1], "PCE set with duplicate items");
        }
        self.uvarint(encs.len() as u64);
        for e in encs {
            self.out.extend_from_slice(&e);
        }
        self
    }
    pub fn finish(self) -> Vec<u8> {
        self.out
    }
}

/// Strict reader.
pub struct Dec<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Dec<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Dec { buf, pos: 0 }
    }
    pub fn pos(&self) -> usize {
        self.pos
    }
    pub fn remaining(&self) -> usize {
        self.buf.len() - self.pos
    }
    pub fn byte(&mut self) -> DResult<u8> {
        let b = *self.buf.get(self.pos).ok_or(DecodeError::Eof)?;
        self.pos += 1;
        Ok(b)
    }
    pub fn uvarint(&mut self) -> DResult<u64> {
        let mut n: u64 = 0;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            let low = (b & 0x7f) as u64;
            if shift >= 64 || (shift == 63 && low > 1) {
                return Err(DecodeError::VarintOverflow);
            }
            n |= low << shift;
            if b & 0x80 == 0 {
                // A final zero group after the first byte is a redundant group.
                if b == 0 && shift > 0 {
                    return Err(DecodeError::NonMinimalVarint);
                }
                return Ok(n);
            }
            shift += 7;
        }
    }
    pub fn raw(&mut self, n: usize) -> DResult<&'a [u8]> {
        if self.remaining() < n {
            return Err(DecodeError::Eof);
        }
        let s = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(s)
    }
    pub fn bytes(&mut self) -> DResult<&'a [u8]> {
        let n = self.uvarint()?;
        if n > self.remaining() as u64 {
            return Err(DecodeError::Eof);
        }
        self.raw(n as usize)
    }
    pub fn fixed<const N: usize>(&mut self, what: &'static str) -> DResult<[u8; N]> {
        let b = self.bytes()?;
        b.try_into().map_err(|_| DecodeError::BadLength { what, len: b.len() })
    }
    pub fn string(&mut self) -> DResult<String> {
        let b = self.bytes()?;
        std::str::from_utf8(b).map(|s| s.to_string()).map_err(|_| DecodeError::BadUtf8)
    }
    pub fn bool(&mut self) -> DResult<bool> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            b => Err(DecodeError::BadBool(b)),
        }
    }
    pub fn nat(&mut self) -> DResult<u128> {
        let b = self.bytes()?;
        if b.first() == Some(&0) {
            return Err(DecodeError::NonMinimalNat);
        }
        if b.len() > 16 {
            return Err(DecodeError::BadLength { what: "nat", len: b.len() });
        }
        Ok(b.iter().fold(0u128, |acc, &x| (acc << 8) | x as u128))
    }
    pub fn option<T>(&mut self, f: impl FnOnce(&mut Dec<'a>) -> DResult<T>) -> DResult<Option<T>> {
        match self.byte()? {
            0 => Ok(None),
            1 => Ok(Some(f(self)?)),
            tag => Err(DecodeError::UnknownTag { what: "option", tag }),
        }
    }
    pub fn list<T>(&mut self, mut f: impl FnMut(&mut Dec<'a>) -> DResult<T>) -> DResult<Vec<T>> {
        let n = self.uvarint()?;
        // Each item takes at least one byte; reject absurd counts before allocating.
        if n > self.remaining() as u64 {
            return Err(DecodeError::Eof);
        }
        let mut v = Vec::with_capacity(n as usize);
        for _ in 0..n {
            v.push(f(self)?);
        }
        Ok(v)
    }
    /// A set: items must appear in strictly increasing order of their encodings.
    pub fn set<T>(&mut self, mut f: impl FnMut(&mut Dec<'a>) -> DResult<T>) -> DResult<Vec<T>> {
        let n = self.uvarint()?;
        if n > self.remaining() as u64 {
            return Err(DecodeError::Eof);
        }
        let mut v = Vec::with_capacity(n as usize);
        let mut prev: Option<&'a [u8]> = None;
        for _ in 0..n {
            let start = self.pos;
            v.push(f(self)?);
            let enc = &self.buf[start..self.pos];
            if let Some(p) = prev {
                if p >= enc {
                    return Err(DecodeError::UnsortedSet);
                }
            }
            prev = Some(enc);
        }
        Ok(v)
    }
    pub fn end(&self) -> DResult<()> {
        if self.remaining() != 0 {
            return Err(DecodeError::Trailing(self.remaining()));
        }
        Ok(())
    }
}

/// A PCE-encodable value.
pub trait Pce: Sized {
    fn encode(&self, e: &mut Enc);
    fn decode(d: &mut Dec<'_>) -> DResult<Self>;

    fn to_pce(&self) -> Vec<u8> {
        let mut e = Enc::new();
        self.encode(&mut e);
        e.out
    }
    /// Decode the whole buffer (trailing bytes rejected).
    fn from_pce(b: &[u8]) -> DResult<Self> {
        let mut d = Dec::new(b);
        let v = Self::decode(&mut d)?;
        d.end()?;
        Ok(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uvarint_matches_leb128_and_p1() {
        // P1's `W.nat`: n < 128 → one byte; else (n % 128) | 0x80, then n / 128.
        fn p1_nat(n: u64, out: &mut Vec<u8>) {
            if n < 128 {
                out.push(n as u8)
            } else {
                out.push((n % 128) as u8 | 0x80);
                p1_nat(n / 128, out)
            }
        }
        for n in [0u64, 1, 127, 128, 255, 300, 16383, 16384, u32::MAX as u64, u64::MAX] {
            let mut e = Enc::new();
            e.uvarint(n);
            let mut p = Vec::new();
            p1_nat(n, &mut p);
            assert_eq!(e.out, p, "n = {n}");
            assert_eq!(Dec::new(&e.out).uvarint().unwrap(), n);
        }
        assert_eq!(Enc::new().uvarint(300).out, vec![0xac, 0x02]);
    }

    #[test]
    fn rejects_non_minimal_and_trailing() {
        assert_eq!(Dec::new(&[0x80, 0x00]).uvarint(), Err(DecodeError::NonMinimalVarint));
        assert_eq!(Dec::new(&[0x81, 0x80, 0x00]).uvarint(), Err(DecodeError::NonMinimalVarint));
        assert!(Dec::new(&[0xff; 11]).uvarint().is_err());
        assert_eq!(Dec::new(&[2]).bool(), Err(DecodeError::BadBool(2)));
        assert_eq!(Dec::new(&[1, 0]).nat(), Err(DecodeError::NonMinimalNat));
        let d = Dec::new(&[0, 1]);
        assert!(d.end().is_err());
    }

    #[test]
    fn nat_and_sets() {
        assert_eq!(Enc::new().nat(0).out, vec![0]);
        assert_eq!(Enc::new().nat(256).out, vec![2, 1, 0]);
        assert_eq!(Dec::new(&[2, 1, 0]).nat().unwrap(), 256);
        let mut e = Enc::new();
        e.set(&[b"b".to_vec(), b"a".to_vec()], |e, x| {
            e.bytes(x);
        });
        assert_eq!(e.out, vec![2, 1, b'a', 1, b'b']);
        let mut d = Dec::new(&[2, 1, b'b', 1, b'a']);
        assert_eq!(d.set(|d| d.bytes().map(|b| b.to_vec())), Err(DecodeError::UnsortedSet));
        let mut d = Dec::new(&[2, 1, b'a', 1, b'a']);
        assert_eq!(d.set(|d| d.bytes().map(|b| b.to_vec())), Err(DecodeError::UnsortedSet));
    }
}
