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
  have hs : Hoare (hiddenClock64 .birthdateExpired : WG.M Int64)
      (fun w => w = k) (fun _ w => w = k) :=
    hoare_liftAmbient (AmbientM.hiddenClock64 .birthdateExpired) (fun w => w = k)
  unfold Hoare at hs
  mvcgen [birthdateTest, hs]

theorem birthdateHasExpired_sameWGWorld (birthday : Int64) (seconds : Nat) :
    SameView (id : WGWorld → WGWorld) (birthdateHasExpired birthday seconds) := by
  apply SameView.of_wp
  intro k
  have hs := (birthdateTest_sameWGWorld birthday seconds).wp (fun k' => k' = k)
  mvcgen [birthdateHasExpired, hs]

theorem branchExpired_sameWGWorld (d : Decision) (birthday : Int64) (seconds : Nat)
    (f : Bool → Bool := id) :
    SameView (id : WGWorld → WGWorld) (branchExpired d birthday seconds f) := by
  apply SameView.of_wp
  intro k
  have hs := (birthdateTest_sameWGWorld birthday seconds).wp (fun k' => k' = k)
  mvcgen [branchExpired, hs, branchCmp, AmbientM.branchCmp]

theorem jitterBelowRekeyTimeout_sameWGWorld (site : HiddenSite) :
    SameView (id : WGWorld → WGWorld) (jitterBelowRekeyTimeout site) := by
  apply SameView.of_wp
  intro k
  have hh : Hoare (hidden site : WG.M (List UInt8)) (fun w => w = k) (fun _ w => w = k) :=
    hoare_liftAmbient (AmbientM.hidden site) (fun w => w = k)
  have hb : Hoare (recordBudget : WG.M Nat) (fun w => w = k) (fun _ w => w = k) :=
    hoare_liftAmbient AmbientM.recordBudget (fun w => w = k)
  have he : Hoare (budgetExhausted "jitter draws" : WG.M Nat)
      (fun w => w = k) (fun _ w => w = k) :=
    hoare_liftAmbient (AmbientM.budgetExhausted "jitter draws") (fun w => w = k)
  unfold Hoare at hh hb he
  mvcgen [jitterBelowRekeyTimeout, hh, hb, he]
  all_goals try exact ((⇓? _ w => ⌜w = k⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem callerJiffies_sameWGWorld (site : HiddenSite) :
    SameView (id : WGWorld → WGWorld) (callerJiffies site) := by
  apply SameView.of_wp
  intro k
  have hh : Hoare (hiddenJiffies site : WG.M UInt64) (fun w => w = k) (fun _ w => w = k) :=
    hoare_liftAmbient (AmbientM.hiddenJiffies site) (fun w => w = k)
  unfold Hoare at hh
  mvcgen [callerJiffies, getAmbient, hh]

end Leanux.Proofs.Framing
