/-!
# Curve25519 (lib/crypto/curve25519*.c): a reference implementation

A cut point with a pure contract: X25519 of RFC 7748. The x86-64 build runs
`curve25519_arch`/`curve25519_base_arch` (WIREGUARD selects
`CRYPTO_CURVE25519_X86`; a static branch picks the BMI2/ADX or the generic
code), and every variant computes this function. The mirror computes it because WireGuard's decisions depend on its
output (`has_identity`, the all-zero precomputed static-static). Constant-time
behavior, and the arithmetic's internal representation, are not mirrored.
-/

namespace Leanux.WG

abbrev Key := List UInt8   -- 32 bytes, as in the C arrays

def p25519 : Nat := 2 ^ 255 - 19

def fromLE (k : Key) : Nat := k.foldr (fun b acc => acc * 256 + b.toNat) 0

def toLE (n : Nat) (len : Nat := 32) : Key :=
  (List.range len).map fun i => (n / 256 ^ i % 256).toUInt8

/-- `curve25519_clamp_secret`. -/
def clamp (k : Key) : Key :=
  k.mapIdx fun i b =>
    if i == 0 then b &&& 248 else if i == 31 then (b &&& 127) ||| 64 else b

private def powMod (b e m : Nat) : Nat := Id.run do
  let mut result := 1
  let mut base := b % m
  let mut exp := e
  while exp > 0 do
    if exp % 2 == 1 then result := result * base % m
    base := base * base % m
    exp := exp / 2
  return result

/-- X25519(k, u) (RFC 7748, section 5). -/
def x25519 (k u : Key) : Key := Id.run do
  let p := p25519
  let scalar := fromLE (clamp k)
  let x1 := fromLE u % 2 ^ 255 % p
  let mut x2 := 1
  let mut z2 := 0
  let mut x3 := x1
  let mut z3 := 1
  let mut swap := 0
  for i in (List.range 255).reverse do
    let bit := scalar / 2 ^ i % 2
    if swap != bit then
      (x2, x3) := (x3, x2)
      (z2, z3) := (z3, z2)
    swap := bit
    let a := (x2 + z2) % p
    let aa := a * a % p
    let b := (x2 + p - z2) % p
    let bb := b * b % p
    let e := (aa + p - bb) % p
    let c := (x3 + z3) % p
    let d := (x3 + p - z3) % p
    let da := d * a % p
    let cb := c * b % p
    x3 := (da + cb) % p * ((da + cb) % p) % p
    z3 := x1 * ((da + p - cb) % p * ((da + p - cb) % p) % p) % p
    x2 := aa * bb % p
    z2 := e * ((aa + 121665 * e) % p) % p
  if swap == 1 then
    (x2, x3) := (x3, x2)
    (z2, z3) := (z3, z2)
  return toLE (x2 * powMod z2 (p - 2) p % p)

def basePoint : Key := toLE 9
def nullPoint : Key := toLE 0

/-- `curve25519(out, secret, basepoint)`: the result, and whether it is not the
    all-zero point (`crypto_memneq(out, curve25519_null_point, ...)`). -/
def curve25519 (secret point : Key) : Key × Bool :=
  let out := x25519 secret point
  (out, out != nullPoint)

end Leanux.WG
