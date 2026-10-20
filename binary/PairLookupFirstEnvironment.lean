import SourceAdapter
import PairLookupFirstAdequacy

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase Callback
local instance : Labels := Image.linkedLabels

/-- The sequential environmental interpretation is explicit. The actual
instruction history is constructed from the execution proof, not supplied
as a successful-run premise. No caller instruction is part of the claim. -/
theorem lookup_first_return (fetch : Int64 → Option Decoded)
    (decoder : AnchoredDecoderAgreement fetch) (services : ServiceDecoderAgreement fetch) (permissions : Permissions)
    (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c initial w query kinds ra answer final} (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : FirstReturnCallPermissions fetch permissions initial ra)
    (checked : Pre n o c initial w query kinds ra)
    (accepted : (Source.indexLookup kinds query).run w=.ok (answer,final)) :
    Eventually (historyStep fetch) (fun t => Post n o c initial ra answer final t.machine ∧
      ActualHistory fetch initial t.history ∧ t.history.getLast?=some t.machine ∧
      BeforeOuterReturn initial ra t.history ∧
      RunEnvironment fetch permissions onlineCPUs externalActions t.history) ⟨initial,[initial]⟩ := by
  have physical := First.lookup_checked fetch decoder (pc_leaf fetch services) (cmp4_leaf fetch services) (const_cmp4_leaf fetch services) (const_cmp1_leaf fetch services) (bh_leaf fetch services) checked accepted
  have history := guarded_history fetch _ _ initial physical [] (by simp)
  have actual := eventually_actual fetch initial _ _ history .start (by simp)
  have last := history_last fetch _ _ (by simp) actual
  apply eventually_weaken (historyStep fetch) _ _ _ _ last
  rintro t ⟨⟨⟨post,interior⟩,actual⟩,last⟩
  have first : BeforeOuterReturn initial ra t.history := by
    intro q member boundary
    exact interior q member boundary.2
  exact ⟨post,actual,last,first,environment,access t.history actual first⟩

#print axioms lookup_first_return
end Binary.Pair.IndexLookup
