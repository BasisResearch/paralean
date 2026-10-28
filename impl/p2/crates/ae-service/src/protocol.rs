//! Read-only RPCs. The enclosing ae-wire signature authenticates every field.
use paralean_store::ae::{AeBundlePage, AeEvent, AeIdentity, AePage};
use paralean_store::pce::{DResult, Dec, DecodeError, Enc, Pce};
use paralean_store::{Id, Kind, ReplicaId};

#[derive(Clone, Debug)]
pub enum Request {
    Hello,
    Changes {
        generation: Id,
        after: Option<Vec<u8>>,
        max_items: u64,
        max_bytes: u64,
    },
    Materialize {
        generation: Id,
        event: AeEvent,
        after_part: Option<u64>,
        max_bytes: u64,
    },
    Fetch {
        generation: Id,
        kind: Kind,
        id: Id,
    },
}

impl Pce for Request {
    fn encode(&self, e: &mut Enc) {
        e.uvarint(1);
        match self {
            Self::Hello => {
                e.byte(0);
            }
            Self::Changes {
                generation,
                after,
                max_items,
                max_bytes,
            } => {
                e.byte(1);
                generation.encode(e);
                e.option(after, |e, b| {
                    e.bytes(b);
                })
                .uvarint(*max_items)
                .uvarint(*max_bytes);
            }
            Self::Materialize {
                generation,
                event,
                after_part,
                max_bytes,
            } => {
                e.byte(2);
                generation.encode(e);
                event.encode(e);
                e.option(after_part, |e, n| {
                    e.uvarint(*n);
                })
                .uvarint(*max_bytes);
            }
            Self::Fetch {
                generation,
                kind,
                id,
            } => {
                e.byte(3);
                generation.encode(e);
                e.string(kind.name());
                id.encode(e);
            }
        }
    }

    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        if d.uvarint()? != 1 {
            return Err(DecodeError::Invalid("anti-entropy RPC version"));
        }
        Ok(match d.byte()? {
            0 => Self::Hello,
            1 => Self::Changes {
                generation: Id::decode(d)?,
                after: d.option(|d| Ok(d.bytes()?.to_vec()))?,
                max_items: d.uvarint()?,
                max_bytes: d.uvarint()?,
            },
            2 => Self::Materialize {
                generation: Id::decode(d)?,
                event: AeEvent::decode(d)?,
                after_part: d.option(Dec::uvarint)?,
                max_bytes: d.uvarint()?,
            },
            3 => Self::Fetch {
                generation: Id::decode(d)?,
                kind: Kind::from_name(&d.string()?).ok_or(DecodeError::Invalid("object kind"))?,
                id: Id::decode(d)?,
            },
            tag => {
                return Err(DecodeError::UnknownTag {
                    what: "anti-entropy RPC",
                    tag,
                })
            }
        })
    }
}

#[derive(Clone, Debug)]
pub enum Response {
    Hello(AeIdentity),
    Changes(AePage),
    Materialize(AeBundlePage),
    Object { kind: Kind, id: Id, length: u64 },
    Missing { kind: Kind, id: Id },
    Error(String),
    /// The source's store GC collected the object (doomed, deleting or gone): the receiver
    /// archives the event instead of retrying (docs/w4-rest-log.md, Design 1).
    Retired { kind: Kind, id: Id },
}

impl Pce for Response {
    fn encode(&self, e: &mut Enc) {
        e.uvarint(1);
        match self {
            Self::Hello(i) => {
                e.byte(0).string(&i.deployment);
                i.replica.encode(e);
                i.config_digest.encode(e);
                i.generation.encode(e);
                e.bytes(&i.transport_public);
            }
            Self::Changes(p) => {
                e.byte(1);
                p.encode(e);
            }
            Self::Materialize(p) => {
                e.byte(2);
                p.encode(e);
            }
            Self::Object { kind, id, length } => {
                e.byte(3).string(kind.name());
                id.encode(e);
                e.uvarint(*length);
            }
            Self::Missing { kind, id } => {
                e.byte(4).string(kind.name());
                id.encode(e);
            }
            Self::Error(s) => {
                e.byte(5).string(s);
            }
            Self::Retired { kind, id } => {
                e.byte(6).string(kind.name());
                id.encode(e);
            }
        }
    }

    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        if d.uvarint()? != 1 {
            return Err(DecodeError::Invalid("anti-entropy RPC version"));
        }
        Ok(match d.byte()? {
            0 => Self::Hello(AeIdentity {
                deployment: d.string()?,
                replica: ReplicaId::decode(d)?,
                config_digest: Id::decode(d)?,
                generation: Id::decode(d)?,
                transport_public: d
                    .bytes()?
                    .try_into()
                    .map_err(|_| DecodeError::Invalid("transport public key"))?,
            }),
            1 => Self::Changes(AePage::decode(d)?),
            2 => Self::Materialize(AeBundlePage::decode(d)?),
            3 => Self::Object {
                kind: Kind::from_name(&d.string()?).ok_or(DecodeError::Invalid("object kind"))?,
                id: Id::decode(d)?,
                length: d.uvarint()?,
            },
            4 => Self::Missing {
                kind: Kind::from_name(&d.string()?).ok_or(DecodeError::Invalid("object kind"))?,
                id: Id::decode(d)?,
            },
            5 => Self::Error(d.string()?),
            6 => Self::Retired {
                kind: Kind::from_name(&d.string()?).ok_or(DecodeError::Invalid("object kind"))?,
                id: Id::decode(d)?,
            },
            tag => {
                return Err(DecodeError::UnknownTag {
                    what: "anti-entropy RPC response",
                    tag,
                })
            }
        })
    }
}
