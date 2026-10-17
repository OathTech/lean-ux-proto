import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Handshake

/-! Original recorded age tests and timer jitter preserve the native WG world.
Their actual Ambient inputs and outputs remain unrestricted. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem birthdateTest_sameWGWorld (birthday : Int64) (seconds : Nat) :
    SameView (id : WGWorld → WGWorld) (birthdateTest birthday seconds) := by
  apply SameView.of_wp
  intro k
  unfold birthdateTest
  exact preserves_bind
    (hoare_liftAmbient (AmbientM.hiddenClock64 .birthdateExpired) (fun w => w = k))
    (fun _ => preserves_pure _)

theorem birthdateHasExpired_sameWGWorld (birthday : Int64) (seconds : Nat) :
    SameView (id : WGWorld → WGWorld) (birthdateHasExpired birthday seconds) := by
  unfold birthdateHasExpired
  exact SameView.bind (birthdateTest_sameWGWorld birthday seconds) (fun _ => SameView.pure _ _)

theorem branchExpired_sameWGWorld (d : Decision) (birthday : Int64) (seconds : Nat)
    (f : Bool → Bool := id) :
    SameView (id : WGWorld → WGWorld) (branchExpired d birthday seconds f) := by
  unfold branchExpired
  apply SameView.bind (birthdateTest_sameWGWorld birthday seconds)
  intro tested
  exact fun k => hoare_liftAmbient (AmbientM.branchCmp d (f tested.1) tested.2.1 tested.2.2)
    (fun w => w = k)

theorem jitterBelowRekeyTimeout_sameWGWorld (site : HiddenSite) :
    SameView (id : WGWorld → WGWorld) (jitterBelowRekeyTimeout site) := by
  apply SameView.of_wp
  intro k
  unfold jitterBelowRekeyTimeout
  apply preserves_bind (hoare_liftAmbient AmbientM.recordBudget (fun w => w = k))
  intro n
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind
  · apply list_view_spec id (fun w => w = k)
    intro i state
    apply preserves_bind (hoare_liftAmbient (AmbientM.hidden site) (fun w => w = k))
    intro bytes
    split <;> exact preserves_pure _
  · intro result
    split
    all_goals first
      | exact preserves_pure _
      | exact hoare_liftAmbient (AmbientM.budgetExhausted "jitter draws") (fun w => w = k)

theorem callerJiffies_sameWGWorld (site : HiddenSite) :
    SameView (id : WGWorld → WGWorld) (callerJiffies site) := by
  apply SameView.of_wp
  intro k
  unfold callerJiffies
  apply preserves_bind (hoare_liftAmbient (get : AmbientM Ambient) (fun w => w = k))
  intro a
  split
  · exact SameView.map (fun initial => hoare_liftAmbient (AmbientM.hiddenJiffies site)
      (fun w => w = initial)) some k
  · exact preserves_pure _

end Leanux.Proofs.Framing
