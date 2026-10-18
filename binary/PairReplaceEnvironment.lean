import PairReplaceAdequacy

namespace Binary.Pair.Replace
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels

/-- The sequential environmental interpretation is explicit. The actual
instruction history is constructed from the execution proof, not supplied
as a successful-run premise. No caller instruction is part of the claim. -/
theorem replace_simulation (fetch : Int64 → Option Decoded)
    (decoder : IndexReplaceDecoderAgreement fetch) (trace : TracePcContract fetch)
    (bh : BhEnableContract fetch) (permissions : Permissions)
    (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c initial w pid kid ra answer final} (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : ReturningCallPermissions fetch permissions initial ra)
    (checked : Pre n o c initial w pid kid ra)
    (accepted : (WG.indexReplaceHandshake pid kid).run w=.ok (answer,final)) :
    Eventually (historyStep fetch) (fun t => Post n o c initial ra answer final t.machine ∧
      ActualHistory fetch initial t.history ∧ t.history.getLast?=some t.machine ∧
      RunEnvironment fetch permissions onlineCPUs externalActions t.history) ⟨initial,[initial]⟩ := by
  have physical := replace_checked fetch decoder trace bh checked accepted
  have history := history_lift fetch _ initial physical [initial]
  have actual := eventually_actual fetch initial _ _ history .start (by simp)
  have last := history_last fetch _ _ (by simp) actual
  apply eventually_weaken (historyStep fetch) _ _ _ _ last
  rintro t ⟨⟨post,actual⟩,last⟩
  exact ⟨post,actual,last,environment,access t.history t.machine actual last post.1⟩

#print axioms replace_simulation
end Binary.Pair.Replace
