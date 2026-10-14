import Leanux.Proofs.Framing.WGAllowedIps

/-! Canonical insertion leaves. Node allocation additionally hides nextNode;
the existing removal mask remains stronger. Both views retain complete tracked
resident objects and their allocation geometry. These source leaves inspect
only explicit node values and the node/device stores, not tracked residents. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def nodeAllocationDevice (d : Device) : Device := {nodeDevice d with nextNode := 0}
def nodeAllocationKernel (k : Kernel) : Kernel :=
  {k with wg := k.wg.map nodeAllocationDevice}
def nodeAllocationView (w : World) : Kernel := nodeAllocationKernel w.k
abbrev SameNodeAllocation (a : M α) := SameView nodeAllocationView a

theorem SameNodeKernel.allocation (h : SameNodeKernel a) : SameNodeAllocation a := by
  have mask (k : Kernel) : nodeAllocationKernel (nodeKernel k) = nodeAllocationKernel k := by
    simp only [nodeAllocationKernel, nodeKernel, Option.map_map]
    rfl
  intro w x v hr
  have he := congrArg nodeAllocationKernel (h w x v hr)
  change nodeAllocationKernel (nodeKernel v.k) = nodeAllocationKernel (nodeKernel w.k) at he
  change nodeAllocationKernel v.k = nodeAllocationKernel w.k
  simpa only [mask] using he

theorem modifyDev_nodeAllocation_spec (P : Kernel → Prop) (f : Device → Device)
    (hf : ∀ d, nodeAllocationDevice (f d) = nodeAllocationDevice d) :
    ⦃fun w => ⌜P (nodeAllocationView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (nodeAllocationView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [nodeAllocationView, nodeAllocationKernel, modifyDev, modifyK,
    Option.map_map, Function.comp_def, hf] using hp

theorem choose_sameKernel (n : AipNode) (key : Nat) : SameKernel (choose n key) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [choose, invariant]

theorem commonBits_sameKernel (n : AipNode) (key bits : Nat) :
    SameKernel (commonBits n key bits) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [commonBits, branch]

theorem prefixMatches_sameKernel (n : AipNode) (key bits : Nat) :
    SameKernel (prefixMatches n key bits) := by
  unfold prefixMatches
  exact sameKernel_bind (commonBits_sameKernel n key bits) (fun _ => sameKernel_pure _)

theorem nodePlacement_sameKernel (trie : Option NodeId) (key cidr bits : Nat) :
    SameKernel (nodePlacement trie key cidr bits) := by
  apply sameKernel_of_wp
  intro k
  have hn := fun id => sameKernel_wp _ (getNode_sameKernel id) (fun s => s = k)
  have hb := fun n i => sameKernel_wp _ (aipBitAt_sameKernel n i) (fun s => s = k)
  have hc := fun n key => sameKernel_wp _ (choose_sameKernel n key) (fun s => s = k)
  have hp := fun n key bits => sameKernel_wp _ (prefixMatches_sameKernel n key bits) (fun s => s = k)
  mvcgen [nodePlacement, hn, hb, hc, hp, branch, branchCmp, invariant]
  all_goals try exact ((⇓? _ w => ⌜w.k = k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem connectNode_sameNodeKernel (slot : Slot) (id : NodeId) :
    SameNodeKernel (connectNode slot id) := by
  unfold connectNode
  exact SameView.bind (SameView.of_sameKernel nodeKernel (getNode_sameKernel id)) (fun n =>
    SameView.bind (setNode_sameNodeKernel id {n with parent := slot}) (fun _ =>
      slotSet_sameNodeKernel slot (some id)))

theorem chooseAndConnectNode_sameNodeKernel (parent node : NodeId) :
    SameNodeKernel (chooseAndConnectNode parent node) := by
  apply SameView.of_wp
  intro s
  have hn := fun id => (SameView.of_sameKernel nodeKernel (getNode_sameKernel id)).wp (fun t => t = s)
  have hc := fun n key => (SameView.of_sameKernel nodeKernel (choose_sameKernel n key)).wp (fun t => t = s)
  have hf := fun slot id => (connectNode_sameNodeKernel slot id).wp (fun t => t = s)
  mvcgen [chooseAndConnectNode, hn, hc, hf]

theorem allocNode_sameNodeAllocation (site : AllocSite) (n : AipNode) :
    SameNodeAllocation (allocNode site n) := by
  apply SameView.of_wp
  intro s
  have hh := (SameView.of_sameKernel nodeAllocationKernel (hiddenAlloc_sameKernel site)).wp (fun t => t = s)
  have hm := modifyDev_nodeAllocation_spec (fun t => t = s)
  mvcgen [allocNode, hh, hm, getDev, getK, invariant]
  all_goals intros; rfl

end Leanux.Proofs.Framing
