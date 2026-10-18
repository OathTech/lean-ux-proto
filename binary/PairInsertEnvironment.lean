import PairInsertAdequacy

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels

/-- Sequential refinement with an actual instruction history and an explicit
permission audit. `ReturningCallPermissions` retains the broader returning-
history quantifier documented in review R2; it is not a first-return claim. -/
theorem insert_simulation (fetch : Int64 → Option Decoded)
    (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch) (bh : BhEnableContract fetch)
    (permissions : Permissions) (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c initial ra config inputAt w owner records answer final}
    (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : ReturningCallPermissions fetch permissions initial ra)
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512) (codeEntry+0x79).toUInt64 inputAt)
    (pre : Pre n o c initial w owner ra config)
    (supplied : w.hidden=some records) (input : inputAt initial.data.dmem records)
    (accepted : (WG.indexInsert owner).run w=.ok (answer,final)) :
    Eventually (historyStep fetch) (fun t => Post n o c initial ra config inputAt answer final t.machine ∧
      ActualHistory fetch initial t.history ∧ t.history.getLast?=some t.machine ∧
      RunEnvironment fetch permissions onlineCPUs externalActions t.history) ⟨initial,[initial]⟩ := by
  have executed := insert_checked fetch decoder trace cmp bh physical coupling pre supplied input accepted
  have history := history_lift fetch _ initial executed [initial]
  have actual := eventually_actual fetch initial _ _ history .start (by simp)
  have last := history_last fetch _ _ (by simp) actual
  apply eventually_weaken (historyStep fetch) _ _ _ _ last
  rintro t ⟨⟨post,actual⟩,last⟩
  exact ⟨post,actual,last,environment,access t.history t.machine actual last post.1⟩

#print axioms insert_simulation
end Binary.Pair.Insert
