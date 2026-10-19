import PairRemoveFirstAdequacy

namespace Binary.Pair.Remove
open Leanux Leanux.WG TrustBase Callback
local instance : Labels := Image.linkedLabels

/-- The sequential environmental interpretation is explicit. The actual
instruction history is constructed from the execution proof, not supplied
as a successful-run premise. No caller instruction is part of the claim. -/
theorem remove_first_return (fetch : Int64 → Option Decoded)
    (decoder : IndexRemoveDecoderAgreement fetch) (services : ServiceDecoderAgreement fetch) (permissions : Permissions)
    (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c initial w owner ra final} (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : FirstReturnCallPermissions fetch permissions initial ra)
    (checked : Pre n o c initial w owner ra)
    (accepted : (WG.indexRemove owner).run w=.ok ((),final)) :
    Eventually (historyStep fetch) (fun t => Post n o c initial ra final t.machine ∧
      ActualHistory fetch initial t.history ∧ t.history.getLast?=some t.machine ∧
      BeforeOuterReturn initial ra t.history ∧
      RunEnvironment fetch permissions onlineCPUs externalActions t.history) ⟨initial,[initial]⟩ := by
  have physical := First.remove_checked fetch decoder (pc_guarded fetch services) (bh_guarded fetch services) checked accepted
  have history := guarded_history fetch _ _ initial physical [] (by simp)
  have actual := eventually_actual fetch initial _ _ history .start (by simp)
  have last := history_last fetch _ _ (by simp) actual
  apply eventually_weaken (historyStep fetch) _ _ _ _ last
  rintro t ⟨⟨⟨post,interior⟩,actual⟩,last⟩
  have first : BeforeOuterReturn initial ra t.history := by
    intro q member boundary
    exact interior q member boundary.2
  exact ⟨post,actual,last,first,environment,access t.history actual first⟩

#print axioms remove_first_return
end Binary.Pair.Remove
