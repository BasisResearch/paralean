module


@[expose] public section

/-! SHA-512 (FIPS 180-4) and Ed25519 signature verification (RFC 8032 §5.1.7) over
`ByteArray`. Field arithmetic uses `Nat` modulo `p = 2^255 - 19`; points use extended
twisted Edwards coordinates. Verification only; nothing here is constant-time. -/

namespace Paralean.Sha512

def K : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

def compress (h : Array UInt64) (blk : ByteArray) (off : Nat) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := Array.mkEmpty 80
  for i in [0:16] do
    let mut x : UInt64 := 0
    for j in [0:8] do
      x := (x <<< 8) ||| (blk.get! (off + 8*i + j)).toUInt64
    w := w.push x
  for i in [16:80] do
    let s0 := rotr w[i-15]! 1 ^^^ rotr w[i-15]! 8 ^^^ (w[i-15]! >>> 7)
    let s1 := rotr w[i-2]! 19 ^^^ rotr w[i-2]! 61 ^^^ (w[i-2]! >>> 6)
    w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for i in [0:80] do
    let S1 := rotr e 14 ^^^ rotr e 18 ^^^ rotr e 41
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let t1 := hh + S1 + ch + K[i]! + w[i]!
    let S0 := rotr a 28 ^^^ rotr a 34 ^^^ rotr a 39
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- SHA-512 digest (64 bytes). -/
def hash (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let mut m := msg
  m := m.push 0x80
  while m.size % 128 != 112 do
    m := m.push 0
  let bits := len * 8
  for i in [0:16] do
    m := m.push (bits >>> (8 * (15 - i))).toUInt8
  let mut h : Array UInt64 := #[0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179]
  for blk in [0:m.size / 128] do
    h := compress h m (128 * blk)
  let mut out := ByteArray.emptyWithCapacity 64
  for x in h do
    for i in [0:8] do
      out := out.push (x >>> (8 * (7 - i)).toUInt64).toUInt8
  return out

end Paralean.Sha512

namespace Paralean.Ed25519

def p : Nat := 2 ^ 255 - 19

/-- Group order of the base point. -/
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

def d2 : Nat := 2 * d % p

/-- A square root of -1 mod p. -/
def sqrtM1 : Nat := 19681161376707505956807079304988542015446066515923890162744021073123829784752

@[inline] def fadd (a b : Nat) : Nat := (a + b) % p
@[inline] def fsub (a b : Nat) : Nat := (a + p - b) % p
@[inline] def fmul (a b : Nat) : Nat := a * b % p

def fpow (b e : Nat) : Nat := Id.run do
  let mut r := 1
  for j in [0:e.log2 + 1] do
    r := fmul r r
    if e.testBit (e.log2 - j) then r := fmul r b
  return r

def finv (a : Nat) : Nat := fpow a (p - 2)

/-- Extended coordinates: x = X/Z, y = Y/Z, x*y = T/Z. -/
structure Point where
  X : Nat
  Y : Nat
  Z : Nat
  T : Nat

def Point.zero : Point := ⟨0, 1, 1, 0⟩

def Point.add (P Q : Point) : Point :=
  let a := fmul (fsub P.Y P.X) (fsub Q.Y Q.X)
  let b := fmul (P.Y + P.X) (Q.Y + Q.X)
  let c := fmul (fmul P.T d2) Q.T
  let dd := fmul (2 * P.Z) Q.Z
  let e := fsub b a
  let f := fsub dd c
  let g := fadd dd c
  let h := fadd b a
  ⟨fmul e f, fmul g h, fmul f g, fmul e h⟩

def Point.double (P : Point) : Point :=
  let a := fmul P.X P.X
  let b := fmul P.Y P.Y
  let c := fmul (2 * P.Z) P.Z
  let h := fadd a b
  let e := fsub h (fmul (P.X + P.Y) (P.X + P.Y))
  let g := fsub a b
  let f := fadd c g
  ⟨fmul e f, fmul g h, fmul f g, fmul e h⟩

def Point.neg (P : Point) : Point := ⟨fsub 0 P.X, P.Y, P.Z, fsub 0 P.T⟩

def Point.ofAffine (x y : Nat) : Point := ⟨x, y, 1, fmul x y⟩

def B : Point := Point.ofAffine
  15112221349535400772501151409588531511454012693041857206046113283949847762202
  46316835694926478169428394003475163141307993866256225615783033603165251855960

/-- Canonical 256-bit encoding (RFC 8032 §5.1.2) as a little-endian integer. -/
def Point.encode (P : Point) : Nat :=
  let zi := finv P.Z
  let x := fmul P.X zi
  let y := fmul P.Y zi
  y + (x % 2) * 2 ^ 255

/-- Decoding per RFC 8032 §5.1.3 (rejects y ≥ p and x = 0 with the sign bit set). -/
def decodePoint (n : Nat) : Option Point :=
  let y := n % 2 ^ 255
  let sign := n / 2 ^ 255
  if y ≥ p then none else
  let y2 := fmul y y
  let u := fsub y2 1
  let v := fadd (fmul d y2) 1
  let v3 := fmul (fmul v v) v
  let x := fmul (fmul u v3) (fpow (fmul (fmul v3 v3) (fmul v u)) ((p - 5) / 8))
  let vx2 := fmul v (fmul x x)
  let x? :=
    if vx2 == u then some x
    else if vx2 == fsub 0 u then some (fmul x sqrtM1)
    else none
  match x? with
  | none => none
  | some x =>
    if x == 0 && sign == 1 then none
    else
      let x := if x % 2 == sign then x else p - x
      some (Point.ofAffine x y)

/-- Little-endian integer from `b[off:off+len]`. -/
def leNat (b : ByteArray) (off len : Nat) : Nat := Id.run do
  let mut n := 0
  for j in [0:len] do
    n := n * 256 + (b.get! (off + len - 1 - j)).toNat
  return n

/-- `[s]P + [t]Q` by Straus–Shamir double-and-add over the 253 bits below `L`. -/
def doubleMul (s : Nat) (P : Point) (t : Nat) (Q : Point) : Point := Id.run do
  let PQ := P.add Q
  let mut R := Point.zero
  for j in [0:253] do
    let i := 252 - j
    R := R.double
    match s.testBit i, t.testBit i with
    | true, true => R := R.add PQ
    | true, false => R := R.add P
    | false, true => R := R.add Q
    | false, false => pure ()
  return R

/-- RFC 8032 §5.1.7 verification, cofactorless: `[S]B = R + [k]A`, checked as
`encode([S]B - [k]A) = R` on the 32 signature bytes (equivalent to decoding R). -/
def verify (publicKey : ByteArray) (msg : ByteArray) (sig : ByteArray) : Bool :=
  if publicKey.size != 32 || sig.size != 64 then false else
  let s := leNat sig 32 32
  if s ≥ L then false else
  match decodePoint (leNat publicKey 0 32) with
  | none => false
  | some A =>
    let h := Sha512.hash ((sig.extract 0 32 ++ publicKey) ++ msg)
    let k := leNat h 0 64 % L
    (doubleMul s B k A.neg).encode == leNat sig 0 32

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def hexToBytes (s : String) : Option ByteArray := do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then none
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    let hi ← hexVal cs[2*i]!
    let lo ← hexVal cs[2*i+1]!
    out := out.push (hi * 16 + lo).toUInt8
  return out

end Paralean.Ed25519
