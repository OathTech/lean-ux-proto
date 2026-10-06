import Leanux.WG.Blake2s

/-!
# Noise primitives: ChaCha20-Poly1305 (RFC 8439), XChaCha20-Poly1305, HMAC-BLAKE2s, the KDF

Reference implementations, like Curve25519 and BLAKE2s: cut points with pure
contracts (lib/crypto and noise.c's `hmac`/`kdf` arithmetic are not mirrored;
`kdf`'s own decisions are, in `Handshake.lean`). The vectors below are
checked when this file builds; they come from the RFC and from the harness's
independent Python implementation (`harness/noise.py`).
-/

namespace Leanux.WG

private def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

private def quarter (s : Array UInt32) (a b c d : Nat) : Array UInt32 := Id.run do
  let mut s := s
  s := s.set! a (s[a]! + s[b]!); s := s.set! d (rotl (s[d]! ^^^ s[a]!) 16)
  s := s.set! c (s[c]! + s[d]!); s := s.set! b (rotl (s[b]! ^^^ s[c]!) 12)
  s := s.set! a (s[a]! + s[b]!); s := s.set! d (rotl (s[d]! ^^^ s[a]!) 8)
  s := s.set! c (s[c]! + s[d]!); s := s.set! b (rotl (s[b]! ^^^ s[c]!) 7)
  return s

private def le32 (bs : List UInt8) (i : Nat) : UInt32 :=
  (List.range 4).foldr (fun k acc => acc <<< 8 ||| (bs[4 * i + k]!).toUInt32) 0

private def bytesOfWords (ws : List UInt32) : List UInt8 :=
  ws.flatMap fun w => (List.range 4).map fun k => (w >>> (8 * k).toUInt32).toUInt8

/-- The 20-round ChaCha permutation (ten double rounds), without the
    feed-forward addition of the input state: the core both `chacha20Block`
    and `hchacha20` use. -/
private def chacha20Permute (init : Array UInt32) : Array UInt32 := Id.run do
  let mut s := init
  for _ in [0:10] do
    s := quarter s 0 4 8 12; s := quarter s 1 5 9 13; s := quarter s 2 6 10 14; s := quarter s 3 7 11 15
    s := quarter s 0 5 10 15; s := quarter s 1 6 11 12; s := quarter s 2 7 8 13; s := quarter s 3 4 9 14
  return s

private def chachaConstants : Array UInt32 := #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

def chacha20Block (key : List UInt8) (counter : Nat) (nonce : List UInt8) : List UInt8 :=
  let init : Array UInt32 := chachaConstants ++
    (List.range 8).toArray.map (le32 key) ++ #[counter.toUInt32] ++ (List.range 3).toArray.map (le32 nonce)
  let s := chacha20Permute init
  bytesOfWords ((List.range 16).map fun i => s[i]! + init[i]!)

/-- HChaCha20 (lib/crypto/chacha.c `hchacha_block_generic`): the permuted
    state's words 0-3 and 12-15, with no feed-forward addition; the 16-byte
    nonce fills words 12-15. -/
def hchacha20 (key nonce16 : List UInt8) : List UInt8 :=
  let s := chacha20Permute (chachaConstants ++ (List.range 8).toArray.map (le32 key) ++
    (List.range 4).toArray.map (le32 nonce16))
  bytesOfWords ([0, 1, 2, 3, 12, 13, 14, 15].map fun i => s[i]!)

def chacha20 (key : List UInt8) (counter : Nat) (nonce data : List UInt8) : List UInt8 :=
  let blocks := (data.length + 63) / 64
  (List.range blocks).flatMap fun i =>
    List.zipWith (· ^^^ ·) ((data.drop (64 * i)).take 64) (chacha20Block key (counter + i) nonce)

private def leNat (bs : List UInt8) : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0
private def natLe (n len : Nat) : List UInt8 := (List.range len).map fun i => (n / 256 ^ i % 256).toUInt8

def poly1305 (key msg : List UInt8) : List UInt8 := Id.run do
  let r := leNat (key.take 16) &&& 0x0ffffffc0ffffffc0ffffffc0fffffff
  let s := leNat (key.drop 16)
  let p := 2 ^ 130 - 5
  let mut acc := 0
  for i in [0:(msg.length + 15) / 16] do
    let block := (msg.drop (16 * i)).take 16
    acc := (acc + leNat (block ++ [1])) * r % p
  return natLe ((acc + s) % 2 ^ 128) 16

private def pad16 (bs : List UInt8) : List UInt8 := bs ++ List.replicate ((16 - bs.length % 16) % 16) 0

private def aeadTag (key nonce aad ciphertext : List UInt8) : List UInt8 :=
  let otk := (chacha20Block key 0 nonce).take 32
  poly1305 otk (pad16 aad ++ pad16 ciphertext ++ natLe aad.length 8 ++ natLe ciphertext.length 8)

def aeadEncrypt (key nonce plaintext aad : List UInt8) : List UInt8 :=
  let ciphertext := chacha20 key 1 nonce plaintext
  ciphertext ++ aeadTag key nonce aad ciphertext

/-- The plaintext iff the tag verifies. -/
def aeadDecrypt (key nonce sealed aad : List UInt8) : Option (List UInt8) :=
  if sealed.length < 16 then none else
  let ciphertext := sealed.take (sealed.length - 16)
  if aeadTag key nonce aad ciphertext != sealed.drop (sealed.length - 16) then none
  else some (chacha20 key 1 nonce ciphertext)

/-- XChaCha20-Poly1305 (lib/crypto/chacha20poly1305.c `xchacha_init`):
    ChaCha20-Poly1305 under the subkey HChaCha20(key, nonce[0:16]) with the
    96-bit nonce 0^4 ‖ nonce[16:24]. -/
def xchachaSubkeyNonce (key nonce : List UInt8) : List UInt8 × List UInt8 :=
  (hchacha20 key (nonce.take 16), List.replicate 4 0 ++ (nonce.drop 16).take 8)

def xchachaEncrypt (key nonce plaintext aad : List UInt8) : List UInt8 :=
  let (k, n) := xchachaSubkeyNonce key nonce
  aeadEncrypt k n plaintext aad

/-- The plaintext iff the tag verifies. -/
def xchachaDecrypt (key nonce sealed aad : List UInt8) : Option (List UInt8) :=
  let (k, n) := xchachaSubkeyNonce key nonce
  aeadDecrypt k n sealed aad

/-- The nonce WireGuard's Noise uses: a zero counter. -/
def noiseNonce : List UInt8 := List.replicate 12 0

def hmacBlake2s (key data : List UInt8) : List UInt8 :=
  let k := key ++ List.replicate (64 - key.length) 0
  let inner := blake2s 32 [] (k.map (· ^^^ 0x36) ++ data)
  blake2s 32 [] (k.map (· ^^^ 0x5c) ++ inner)

/-- `kdf` (noise.c:344-390): HKDF with HMAC-BLAKE2s, `n` outputs. -/
def kdfOutputs (chainingKey data : List UInt8) (n : Nat) : List (List UInt8) := Id.run do
  let secret := hmacBlake2s chainingKey data
  let mut out := []
  let mut prev : List UInt8 := []
  for i in [1:n + 1] do
    prev := hmacBlake2s secret (prev ++ [i.toUInt8])
    out := out ++ [prev]
  return out

def noiseHash (data : List UInt8) : List UInt8 := blake2s 32 [] data

def NOISE_CONSTRUCTION : List UInt8 := "Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s".toUTF8.toList
def NOISE_IDENTIFIER : List UInt8 := "WireGuard v1 zx2c4 Jason@zx2c4.com".toUTF8.toList
/-- `handshake_init_chaining_key` and `handshake_init_hash` (wg_noise_init). -/
def handshakeInitChainingKey : List UInt8 := noiseHash NOISE_CONSTRUCTION
def handshakeInitHash : List UInt8 := noiseHash (handshakeInitChainingKey ++ NOISE_IDENTIFIER)

private def hex (bs : List UInt8) : String :=
  String.join (bs.map fun b => let d := "0123456789abcdef".toList; String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])

private def unhex (s : String) : List UInt8 :=
  let v (c : Char) := if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List UInt8
    | a :: b :: r => UInt8.ofNat (v a * 16 + v b) :: go r
    | _ => []
  go s.toList

-- RFC 8439 section 2.8.2
#guard hex (aeadEncrypt ((List.range' 0x80 32).map UInt8.ofNat) (unhex "070000004041424344454647")
    "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.".toUTF8.toList
    (unhex "50515253c0c1c2c3c4c5c6c7")) ==
  "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b61161ae10b594f09e26a7e902ecbd0600691"
-- harness/noise.py
#guard hex (aeadEncrypt ((List.range 32).map UInt8.ofNat) noiseNonce (List.replicate 32 7) (List.replicate 32 1)) ==
  "1fbf4536aae1a1d614665b66a8444920ffb6f4f2e6aa5c5bebfffb152d32725bd12b0ee8509122bf07e0b8765801bcc6"
#guard aeadDecrypt ((List.range 32).map UInt8.ofNat) noiseNonce
  (unhex "1fbf4536aae1a1d614665b66a8444920ffb6f4f2e6aa5c5bebfffb152d32725bd12b0ee8509122bf07e0b8765801bcc6")
  (List.replicate 32 1) == some (List.replicate 32 7)
#guard aeadDecrypt ((List.range 32).map UInt8.ofNat) noiseNonce
  (unhex "1fbf4536aae1a1d614665b66a8444920ffb6f4f2e6aa5c5bebfffb152d32725bd12b0ee8509122bf07e0b8765801bcc7")
  (List.replicate 32 1) == none
#guard hex (hmacBlake2s ((List.range 32).map UInt8.ofNat) "abc".toUTF8.toList) ==
  "82623be5bc0a391b24dce53e67d028eff92d586de0485ac37822e597d049c74f"
#guard (kdfOutputs ((List.range 32).map UInt8.ofNat) "data".toUTF8.toList 3).map hex ==
  ["42a038507e272afffcea6d2d2a98346bcedbd242b0cab0cb664dd6dd486e38db",
   "cdc87247bb6325709c399eb10f937003b5f85b4e29f3d8016f4c10f9d8b5655c",
   "37009b4aeed47b33230402a8d0d209dc1c8f0762b16958d4b7362c72ff2fdacc"]
-- draft-irtf-cfrg-xchacha-03 section 2.2.1 (HChaCha20) and appendix A.3.1
-- (XChaCha20-Poly1305); libsodium agrees on both
#guard hex (hchacha20 ((List.range 32).map UInt8.ofNat) (unhex "000000090000004a0000000031415927")) ==
  "82413b4227b27bfed30e42508a877d73a0f9e4d58a74a853c12ec41326d3ecdc"
#guard hex (xchachaEncrypt ((List.range' 0x80 32).map UInt8.ofNat) ((List.range' 0x40 24).map UInt8.ofNat)
    "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.".toUTF8.toList
    (unhex "50515253c0c1c2c3c4c5c6c7")) ==
  "bd6d179d3e83d43b9576579493c0e939572a1700252bfaccbed2902c21396cbb731c7f1b0b4aa6440bf3a82f4eda7e39ae64c6708c54c216cb96b72e1213b4522f8c9ba40db5d945b11b69b982c1bb9e3f3fac2bc369488f76b2383565d3fff921f9664c97637da9768812f615c68b13b52ec0875924c1c7987947deafd8780acf49"
-- a cookie-sized vector (harness/noise.py, libsodium): 16-byte cookie, 16-byte AAD
#guard xchachaDecrypt ((List.range 32).map UInt8.ofNat) ((List.range' 0x40 24).map UInt8.ofNat)
  (unhex "d33e0277d7e77e1188f380b9a89b6295f5e04a578ccbd2023f1c0eeeb9ea6e52") (List.replicate 16 1) ==
  some (List.replicate 16 7)
#guard xchachaDecrypt ((List.range 32).map UInt8.ofNat) ((List.range' 0x40 24).map UInt8.ofNat)
  (unhex "d33e0277d7e77e1188f380b9a89b6295f5e04a578ccbd2023f1c0eeeb9ea6e52") (List.replicate 16 0) == none
#guard hex handshakeInitChainingKey == "60e26daef327efc02ec335e2a025d2d016eb4206f87277f52d38d1988b78cd36"
#guard hex handshakeInitHash == "2211b361081ac566691243db458ad5322d9c6c662293e8b70ee19c65ba079ef3"

end Leanux.WG
