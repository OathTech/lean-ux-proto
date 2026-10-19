import Leanux.Proofs.WG.Config.RequestOrderSource

/-! State-indexed rule for the existing completed-receipt observer. Extracted once from the owned key-header rule; the observer is unchanged. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

theorem record_state_rule (attrs : DeviceAttrs) (kind : Kind)
    {P : List Receipt→WGWorld→Ambient→Prop} {S : List Receipt→Prop}
    {Q : Int→List Receipt→WGWorld→Ambient→Prop}
    (safe : ∀h g a,P h g a→S h)
    (normal : ∀h g a ret v b,P h g a→((action attrs kind).run g).run a=.ok ((ret,v),b)→
      let r:=receipt kind ⟨ret,g,v,a,b⟩
      S (h++[r]) ∧ Q ret (h++[r]) v b) :
    StatePrefixEnsures P S (record attrs kind) Q := by
  intro g a h pre
  have source:=runWGPrefix_receiptWGObserved
    (liftWGPrefix (action attrs kind)) (receipt kind) g a h
  rw [runWGPrefix_lift] at source
  simp only [runWGPrefix,runStatePrefix] at source
  unfold record
  rw [source]
  cases run : ((action attrs kind).run g).run a with
  | error stop=>exact ⟨[],by simp,safe h g a pre,trivial⟩
  | ok out=>
    rcases out with ⟨⟨ret,v⟩,b⟩
    exact ⟨[receipt kind ⟨ret,g,v,a,b⟩],rfl,normal h g a ret v b pre run⟩

end Leanux.Proofs.WG.Config.RequestOrder
