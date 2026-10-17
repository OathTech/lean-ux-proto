import Leanux.Proofs.WG.Progress.PowEvaluationSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress
open Leanux.WG
/-- The original finite ladder, ending immediately before modular inversion. -/
def x25519Ladder (k u : Key) : Nat × Nat := Id.run do
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
  return (x2, z2)

/-- Exact source factor; no claim about the cryptographic specification. -/
theorem x25519_ladder_source (k u : Key) :
    x25519 k u =
      toLE ((x25519Ladder k u).1 *
        originalPowMod (x25519Ladder k u).2 (p25519 - 2) p25519 % p25519) := by
  dsimp only [x25519, x25519Ladder, Id.run, Bind.bind, Pure.pure]
  split <;> rfl

/-- Successful finite inversion evaluation determines the original X25519 output. -/
theorem x25519_of_evaluation (k u : Key) (fuel : Nat) (final : PowState)
    (evaluated : powEval p25519 fuel
      (1, (x25519Ladder k u).2 % p25519, p25519 - 2) = some final) :
    x25519 k u = toLE ((x25519Ladder k u).1 * final.1 % p25519) := by
  rw [x25519_ladder_source, powMod_of_evaluation _ _ _ fuel final evaluated]

end Leanux.Proofs.WG.Progress
