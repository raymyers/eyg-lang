/-!
# SHA-256, base32, and CIDv1 for the IR codec

Supports `ir_suite.json`'s `cid` field. Mirrors `eyg/ir/cid.gleam` +
`multiformats` glue: the canonical dag-json block bytes are hashed with
SHA-256, wrapped as a sha2-256 multihash, prefixed with the CIDv1 version and
the dag-json codec (`0x0129` = 297), and rendered as multibase base32-lower
(prefix `b`).

The dag-json **block bytes** themselves are produced in the harness via
`Lean.Json.compress` over a sorted-key object (canonical for the single-ASCII-
char node keys the IR uses); this file only turns those bytes into a CID string.
-/

namespace Eyg.Ir.Cid

/-! ## SHA-256 -/

private def k256 : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def beWord (b : ByteArray) (i : Nat) : UInt32 :=
  (b[i]!.toUInt32 <<< 24) ||| (b[i+1]!.toUInt32 <<< 16) |||
  (b[i+2]!.toUInt32 <<< 8) ||| b[i+3]!.toUInt32

/-- Pad a message per FIPS 180-4: `0x80`, zeros, then 64-bit big-endian bit length. -/
private def pad (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let bitLen : Nat := len * 8
  let mut out := msg.push 0x80
  while out.size % 64 ≠ 56 do
    out := out.push 0x00
  -- 64-bit big-endian bit length
  for i in [0:8] do
    out := out.push (((bitLen >>> ((7 - i) * 8)) &&& 0xFF).toUInt8)
  return out

/-- SHA-256 digest (32 bytes) of a byte array. -/
def sha256 (msg : ByteArray) : ByteArray := Id.run do
  let data := pad msg
  let mut h0 : UInt32 := 0x6a09e667
  let mut h1 : UInt32 := 0xbb67ae85
  let mut h2 : UInt32 := 0x3c6ef372
  let mut h3 : UInt32 := 0xa54ff53a
  let mut h4 : UInt32 := 0x510e527f
  let mut h5 : UInt32 := 0x9b05688c
  let mut h6 : UInt32 := 0x1f83d9ab
  let mut h7 : UInt32 := 0x5be0cd19
  let nblocks := data.size / 64
  for blk in [0:nblocks] do
    let base := blk * 64
    let mut w : Array UInt32 := Array.replicate 64 0
    for t in [0:16] do
      w := w.set! t (beWord data (base + t * 4))
    for t in [16:64] do
      let s0 := rotr (w[t-15]!) 7 ^^^ rotr (w[t-15]!) 18 ^^^ (w[t-15]! >>> 3)
      let s1 := rotr (w[t-2]!) 17 ^^^ rotr (w[t-2]!) 19 ^^^ (w[t-2]! >>> 10)
      w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
    let mut a := h0; let mut b := h1; let mut c := h2; let mut d := h3
    let mut e := h4; let mut f := h5; let mut g := h6; let mut h := h7
    for t in [0:64] do
      let σ1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let t1 := h + σ1 + ch + k256[t]! + w[t]!
      let σ0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := σ0 + maj
      h := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
    h0 := h0 + a; h1 := h1 + b; h2 := h2 + c; h3 := h3 + d
    h4 := h4 + e; h5 := h5 + f; h6 := h6 + g; h7 := h7 + h
  let mut out := ByteArray.empty
  for hw in [h0, h1, h2, h3, h4, h5, h6, h7] do
    for i in [0:4] do
      out := out.push (((hw >>> ((3 - i).toUInt32 * 8)) &&& 0xFF).toUInt8)
  return out

/-! ## base32 (lower, RFC 4648, no padding) -/

private def b32alphabet : Array Char :=
  "abcdefghijklmnopqrstuvwxyz234567".toList.toArray

/-- Encode bytes as lowercase base32 without padding. -/
def base32 (bytes : ByteArray) : String := Id.run do
  let mut out := ""
  let mut acc : Nat := 0
  let mut nbits : Nat := 0
  for b in bytes.toList do
    acc := (acc <<< 8) ||| b.toNat
    nbits := nbits + 8
    while nbits ≥ 5 do
      nbits := nbits - 5
      out := out.push b32alphabet[((acc >>> nbits) &&& 0x1F)]!
  if nbits > 0 then
    out := out.push b32alphabet[((acc <<< (5 - nbits)) &&& 0x1F)]!
  return out

/-! ## CIDv1 -/

/-- Encode a `Nat` as an unsigned LEB128 varint. -/
private def varint (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut v := n
  repeat
    let byte := v &&& 0x7F
    v := v >>> 7
    if v == 0 then
      out := out.push byte.toUInt8
      break
    else
      out := out.push (byte ||| 0x80).toUInt8
  return out

/-- The dag-json multicodec code (`0x0129` = 297). -/
def dagJsonCodec : Nat := 0x0129

/-- Build a CIDv1 string from the canonical block bytes: SHA-256 → sha2-256
multihash → `0x01`/codec/multihash → multibase base32-lower (`b` prefix). -/
def cidOfBlock (block : ByteArray) : String :=
  let digest := sha256 block
  -- multihash: <sha2-256 = 0x12> <len = 0x20> <digest>
  let multihash := (ByteArray.empty.push 0x12 |>.push 0x20) ++ digest
  -- cid bytes: <version 0x01> <codec varint> <multihash>
  let cidBytes := ((ByteArray.empty.push 0x01) ++ varint dagJsonCodec) ++ multihash
  "b" ++ base32 cidBytes

/-! ## Self-check -/

-- SHA-256("abc")
#guard (sha256 "abc".toUTF8).toList.map (fun b => b.toNat) ==
  [0xba,0x78,0x16,0xbf,0x8f,0x01,0xcf,0xea,0x41,0x41,0x40,0xde,0x5d,0xae,0x22,0x23,
   0xb0,0x03,0x61,0xa3,0x96,0x17,0x7a,0x9c,0xb4,0x10,0xff,0x61,0xf2,0x00,0x15,0xad]
-- SHA-256("") empty
#guard (sha256 "".toUTF8).toList.map (fun b => b.toNat) ==
  [0xe3,0xb0,0xc4,0x42,0x98,0xfc,0x1c,0x14,0x9a,0xfb,0xf4,0xc8,0x99,0x6f,0xb9,0x24,
   0x27,0xae,0x41,0xe4,0x64,0x9b,0x93,0x4c,0xa4,0x95,0x99,0x1b,0x78,0x52,0xb8,0x55]

end Eyg.Ir.Cid
