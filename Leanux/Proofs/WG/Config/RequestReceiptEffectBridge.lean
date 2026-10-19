import Leanux.Proofs.WG.Config.RequestRefusalEffects
import Leanux.Proofs.WG.Config.RequestOrderReceiptBridge

/-! Actual completed receipt contracts and the native post-port cut. The fixed Ambient parameter is used only to project WireGuard state. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

theorem Valid.ensures {attrs : DeviceAttrs} {r : Receipt} {kind : Kind}
    (valid : Valid attrs r) (selected : r.kind = kind)
    {P : Campaign2.Snapshot → Prop} {Q : Int → Campaign2.Snapshot → Prop}
    (contract : Campaign2.Ensures (action attrs kind) P Q) (pre : P r.before) :
    Q r.result r.after := by
  obtain ⟨native,run,same⟩ := valid
  rw [selected] at run same
  have post := contract native.before native.ambientBefore native.value native.after
    native.ambientAfter (by simpa only [← same,receipt] using pre) run
  simpa only [← same,receipt] using post

theorem pureMap_ensures {α : Type} {a : WG.M α} (f : α → Int)
    {P : Campaign2.Snapshot → Prop} {Q : α → Campaign2.Snapshot → Prop}
    (contract : Campaign2.Ensures a P Q) :
    Campaign2.Ensures (do let value ← a; pure (f value)) P
      (fun value final => ∃ input, value = f input ∧ Q input final) := by
  intro w ambient value v after pre run
  cases step : (a.run w).run ambient with
  | error stop =>
    simp only [StateT.run_bind,StateT.run_pure,step] at run
    cases run
  | ok out =>
    rcases out with ⟨⟨input,middle⟩,next⟩
    simp only [StateT.run_bind,StateT.run_pure,step] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact ⟨input,rfl,contract w ambient input middle next pre step⟩

def AfterPortRecord (a : Ambient) (port : Nat) (ret : Int) (h : List Receipt) (w : WGWorld) : Prop :=
  ∃ old r, h = old ++ [r] ∧ NoRefusal old ∧ r.kind = .port port ∧ r.result = ret ∧
    r.after.wg = (Campaign2.snapshot w a).wg

theorem AfterPortRecord.final {a : Ambient} {port : Nat} {ret : Int} {h : List Receipt} {w : WGWorld}
    (point : AfterPortRecord a port ret h w) :
    RefusalFinal ret h (Campaign2.snapshot w a).wg := by
  obtain ⟨old,r,rfl,prior,kind,result,after⟩ := point
  intro other member refused
  rcases List.mem_append.mp member with earlier | last
  · exact False.elim (prior other earlier refused)
  · have same := List.mem_singleton.mp last
    subst other
    exact ⟨result,after⟩

theorem AfterPortRecord.zero {a : Ambient} {port : Nat} {ret : Int} {h : List Receipt} {w : WGWorld}
    (point : AfterPortRecord a port ret h w) (zero : ret = 0) : NoRefusal h := by
  obtain ⟨old,r,rfl,prior,kind,result,after⟩ := point
  apply prior.append
  intro other member refused
  have same := List.mem_singleton.mp member
  subst other
  exact refused.2 (result.trans zero)

end Leanux.Proofs.WG.Config.RequestOrder
