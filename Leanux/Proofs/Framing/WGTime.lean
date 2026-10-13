import Leanux.Proofs.Framing.KernelEffects
import Leanux.WG.Peer

/-! Original recorded age tests preserve the complete kernel. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem birthdateTest_sameKernel (birthday : Int64) (seconds : Nat) :
    SameKernel (birthdateTest birthday seconds) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (hiddenClock64_sameKernel .birthdateExpired) (fun k' => k' = k)
  mvcgen [birthdateTest, hs]

theorem birthdateHasExpired_sameKernel (birthday : Int64) (seconds : Nat) :
    SameKernel (birthdateHasExpired birthday seconds) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (birthdateTest_sameKernel birthday seconds) (fun k' => k' = k)
  mvcgen [birthdateHasExpired, hs]

theorem branchExpired_sameKernel (d : Decision) (birthday : Int64) (seconds : Nat)
    (f : Bool → Bool := id) : SameKernel (branchExpired d birthday seconds f) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (birthdateTest_sameKernel birthday seconds) (fun k' => k' = k)
  mvcgen [branchExpired, hs, branchCmp]

end Leanux.Proofs.Framing
