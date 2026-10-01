import Leanux.WG.Curve25519

/-!
# BLAKE2s (RFC 7693): a reference implementation

A cut point with a pure contract, like Curve25519. The receive path's
decisions depend on its output: `wg_cookie_validate_packet` compares MAC1, a
keyed BLAKE2s-128 of the message, under a key that is BLAKE2s-256 of
"mac1----" and the device's public key (cookie.c `precompute_key`). The
kernel's implementation (lib/crypto/blake2s*.c) is not mirrored. The vectors
below are checked when this file builds; they come from Python's `hashlib`.
-/

namespace Leanux.WG

private def iv : Array UInt32 := #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
  0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

private def sigma : Array (Array Nat) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

private def mix (v : Array UInt32) (a b c d : Nat) (x y : UInt32) : Array UInt32 := Id.run do
  let mut v := v
  v := v.set! a (v[a]! + v[b]! + x)
  v := v.set! d (rotr (v[d]! ^^^ v[a]!) 16)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr (v[b]! ^^^ v[c]!) 12)
  v := v.set! a (v[a]! + v[b]! + y)
  v := v.set! d (rotr (v[d]! ^^^ v[a]!) 8)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr (v[b]! ^^^ v[c]!) 7)
  return v

/-- The little-endian 32-bit word at `i` of a 64-byte block. -/
private def word (block : Array UInt8) (i : Nat) : UInt32 :=
  (List.range 4).foldr (fun k acc => acc <<< 8 ||| (block[4 * i + k]!).toUInt32) 0

private def compress (h : Array UInt32) (block : Array UInt8) (t : Nat) (last : Bool) : Array UInt32 := Id.run do
  let m := (List.range 16).toArray.map (word block)
  let mut v := h ++ iv
  v := v.set! 12 (v[12]! ^^^ (t % 2 ^ 32).toUInt32)
  v := v.set! 13 (v[13]! ^^^ (t / 2 ^ 32).toUInt32)
  if last then v := v.set! 14 (v[14]! ^^^ 0xFFFFFFFF)
  for r in [0:10] do
    let s := sigma[r]!
    v := mix v 0 4 8 12 m[s[0]!]! m[s[1]!]!
    v := mix v 1 5 9 13 m[s[2]!]! m[s[3]!]!
    v := mix v 2 6 10 14 m[s[4]!]! m[s[5]!]!
    v := mix v 3 7 11 15 m[s[6]!]! m[s[7]!]!
    v := mix v 0 5 10 15 m[s[8]!]! m[s[9]!]!
    v := mix v 1 6 11 12 m[s[10]!]! m[s[11]!]!
    v := mix v 2 7 8 13 m[s[12]!]! m[s[13]!]!
    v := mix v 3 4 9 14 m[s[14]!]! m[s[15]!]!
  return (List.range 8).toArray.map fun i => h[i]! ^^^ v[i]! ^^^ v[i + 8]!

/-- BLAKE2s with an `outLen`-byte digest (1–32) and an optional key (0–32 bytes). -/
def blake2s (outLen : Nat) (key : List UInt8) (data : List UInt8) : List UInt8 := Id.run do
  let param : UInt32 := (0x01010000 : UInt32) ||| (key.length.toUInt32 <<< (8 : UInt32)) ||| outLen.toUInt32
  let mut h := iv.set! 0 (iv[0]! ^^^ param)
  let input := (if key.isEmpty then [] else key ++ List.replicate (64 - key.length) 0) ++ data
  let blocks := if input.isEmpty then 1 else (input.length + 63) / 64
  for i in [0:blocks] do
    let chunk := (input.drop (64 * i)).take 64
    let block := (chunk ++ List.replicate (64 - chunk.length) 0).toArray
    let last := i + 1 == blocks
    h := compress h block (if last then input.length else 64 * (i + 1)) last
  let bytes := h.toList.flatMap fun w => (List.range 4).map fun k => (w >>> (8 * k).toUInt32).toUInt8
  return bytes.take outLen

private def hex (bs : List UInt8) : String :=
  String.join (bs.map fun b => let d := "0123456789abcdef".toList; String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])

private def unhex (s : String) : List UInt8 :=
  let v (c : Char) := if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List UInt8
    | a :: b :: r => UInt8.ofNat (v a * 16 + v b) :: go r
    | _ => []
  go s.toList

#guard hex (blake2s 32 [] "abc".toUTF8.toList) == "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"
#guard hex (blake2s 32 [] []) == "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9"
#guard hex (blake2s 32 [] ((List.range 200).map UInt8.ofNat)) == "6d244e1a06ce4ef578dd0f63aff0936706735119ca9c8d22d86c801414ab9741"
#guard hex (blake2s 16 ((List.range 32).map UInt8.ofNat) ((List.range 100).map UInt8.ofNat)) == "0b67d33f8b859c3157fbabd9e6e47ed0"
-- WireGuard's MAC1 key for the public key of 11..11, and a MAC1
#guard hex (blake2s 32 [] ("mac1----".toUTF8.toList ++ unhex "7b4e909bbe7ffe44c465a220037d608ee35897d31ef972f07f74892cb0f73f13")) ==
  "2f8377a0268a9731b6008d714f7cb7f4d3894c759cec65269f872f64619794f5"
#guard hex (blake2s 16 (unhex "2f8377a0268a9731b6008d714f7cb7f4d3894c759cec65269f872f64619794f5")
  ([1, 0, 0, 0] ++ (List.range' 4 112).map UInt8.ofNat)) == "336484fb4e79952500a5dbd56867503e"
#guard hex (blake2s 16 (unhex "2f8377a0268a9731b6008d714f7cb7f4d3894c759cec65269f872f64619794f5") (List.replicate 128 0)) ==
  "710a85b23ec69c645958cd0c3a54bd40"

end Leanux.WG
