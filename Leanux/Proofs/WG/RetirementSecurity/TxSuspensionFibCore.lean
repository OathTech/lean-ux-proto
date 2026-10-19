import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionCreate

/-! Native IPv4 trie operations retain suspended workers. This frame uses
actual record consumers, including failed allocations and bounded recursive
resize paths; it does not assume an arbitrary routing or ambient action is quiet. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Fib
open Leanux Leanux.Net Leanux.Net.Fib
open Leanux.Proofs.Framing Lifetimes Queues

theorem env_result (site : EnvSite) : Keeps (envOk site : Net.M Bool) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.envOk at run
  simp only [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  obtain ⟨_,u,written,returned⟩:=tail
  cases written
  cases returned
  rfl

theorem get_trie  : Keeps (getTrie) := by
  suspension_source [getTrie] using [table]

theorem set_trie (t : Trie) : Keeps (setTrie t) := by
  suspension_source [setTrie] using [table_modify]

theorem tnode_full (tn : KeyVector) (n : Option KeyVector) : Keeps (tnodeFull tn n) := by
  suspension_source [tnodeFull] using [branch,compare,invariant]

theorem empty_inc (tn : KeyVector) : Keeps (emptyChildInc tn) := by
  suspension_source [emptyChildInc] using [compare]

theorem empty_dec (tn : KeyVector) : Keeps (emptyChildDec tn) := by
  suspension_source [emptyChildDec] using [compare]

theorem put_child (tn : KeyVector) (i : Nat) (n : Option KeyVector) : Keeps (putChild tn i n) := by
  suspension_source [putChild] using [branch,compare,invariant,empty_inc,empty_dec,tnode_full]

theorem put_root (tp : KeyVector) (key : Nat) (n : Option KeyVector) : Keeps (putChildRoot tp key n) := by
  suspension_source [putChildRoot] using [compare,put_child]

theorem tnode_new (key pos bits : Nat) : Keeps (tnodeNew key pos bits) := by
  suspension_source [tnodeNew] using [branch,env_result,invariant,unsupported]

theorem leaf_new (key : Nat) (fa : FibAlias) : Keeps (leafNew key fa) := by
  suspension_source [leafNew] using [branch,env_result]

theorem update_suffix (tn : KeyVector) : Keeps (updateSuffix tn) := by
  suspension_source [updateSuffix] using [branch,compare,invariant]

theorem should_inflate (tp tn : KeyVector) : Keeps (shouldInflate tp tn) := by
  suspension_source [shouldInflate] using [compare]

theorem should_halve (tp tn : KeyVector) : Keeps (shouldHalve tp tn) := by
  suspension_source [shouldHalve] using [compare]

theorem should_collapse (tn : KeyVector) : Keeps (shouldCollapse tn) := by
  suspension_source [shouldCollapse] using [branch,compare]

theorem tnode_free (count : Nat) : Keeps (tnodeFree count) := by
  suspension_source [tnodeFree] using [branch,invariant]

theorem collapse_node (tp : KeyVector) (cindex : Nat) (old : KeyVector) : Keeps (collapse tp cindex old) := by
  suspension_source [collapse] using [branch,compare,put_root]

theorem update_children (fuel : Nat) (tn : KeyVector) : Keeps (updateChildren fuel tn) := by
  induction fuel generalizing tn with
  | zero=>exact exhausted _
  | succ fuel ih=>
    rw [updateChildren]
    suspension_source [] using [branch,invariant,ih]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Fib
