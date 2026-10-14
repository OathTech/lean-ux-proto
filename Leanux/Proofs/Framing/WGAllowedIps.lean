import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.KernelEffects
import Leanux.Proofs.WG.AllowedIps.RemovalSource

/-! Canonical node-only frames. The mask omits nodes and trie roots/sequence,
but retains complete resident stores, device presence and every frontier,
including nextNode. Source inspection separately establishes that these
helpers do not resolve peers, keypairs or packets. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def nodeDevice (d : Device) : Device :=
  {d with nodes := {}, peerAllowedips := {}}

def nodeKernel (k : Kernel) : Kernel := {k with wg := k.wg.map nodeDevice}
def nodeKernelView (w : World) : Kernel := nodeKernel w.k
abbrev SameNodeKernel (a : M α) := SameView nodeKernelView a

theorem modifyDev_node_spec (P : Kernel → Prop) (f : Device → Device)
    (hf : ∀ d, nodeDevice (f d) = nodeDevice d) :
    ⦃fun w => ⌜P (nodeKernelView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (nodeKernelView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [nodeKernelView, nodeKernel, modifyDev, modifyK,
    Option.map_map, Function.comp_def, hf] using hp

theorem getNode_sameKernel (id : NodeId) : SameKernel (getNode id) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [getNode, getDev, getK, invariant]

theorem aipBitAt_sameKernel (n : AipNode) (i : Nat) : SameKernel (n.bitAt i) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [AipNode.bitAt, invariant]

theorem setNode_sameNodeKernel (id : NodeId) (n : AipNode) : SameNodeKernel (setNode id n) := by
  apply SameView.of_wp
  intro s
  exact modifyDev_node_spec (fun x => x = s) _ (fun _ => rfl)

theorem freeNode_sameNodeKernel (id : NodeId) : SameNodeKernel (freeNode id) := by
  unfold freeNode
  apply SameView.bind (SameView.of_sameKernel nodeKernel (getNode_sameKernel id))
  intro _
  apply SameView.of_wp
  intro s
  exact modifyDev_node_spec (fun x => x = s) _ (fun _ => rfl)

theorem slotGet_sameKernel (s : Slot) : SameKernel (slotGet s) := by
  apply sameKernel_of_wp
  intro k
  have hn := fun id => sameKernel_wp _ (getNode_sameKernel id) (fun x => x = k)
  have hb := fun n i => sameKernel_wp _ (aipBitAt_sameKernel n i) (fun x => x = k)
  mvcgen [slotGet, getDev, getK, invariant, hn, hb]

theorem slotSet_sameNodeKernel (s : Slot) (v : Option NodeId) : SameNodeKernel (slotSet s v) := by
  apply SameView.of_wp
  intro initial
  have hn := fun id => (SameView.of_sameKernel nodeKernel (getNode_sameKernel id)).wp (fun x => x = initial)
  have hs := fun id n => (setNode_sameNodeKernel id n).wp (fun x => x = initial)
  have hm := modifyDev_node_spec (fun x => x = initial)
  mvcgen [slotSet, hn, hs, hm, invariant]
  all_goals intros; rfl

theorem subtree_sameKernel (id : NodeId) : SameKernel (subtree id) := by
  apply sameKernel_of_wp
  intro k
  have hn := fun id => sameKernel_wp _ (getNode_sameKernel id) (fun x => x = k)
  have hl (α β : Type) := list_view_spec (fun w => w.k) (α := α) (β := β) (fun s => s = k)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, subtree, hn, getDev, getK, invariant]
  all_goals try exact ((⇓? _ w => ⌜w.k = k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem removeParentTail_sameNodeKernel (parent : NodeId) (sibling : Option NodeId) :
    SameNodeKernel (WG.AllowedIps.removeParentTail parent sibling) := by
  apply SameView.of_wp
  intro initial
  have hn := fun id => (SameView.of_sameKernel nodeKernel (getNode_sameKernel id)).wp (fun x => x = initial)
  have hs := fun id n => (setNode_sameNodeKernel id n).wp (fun x => x = initial)
  have hslot := fun s v => (slotSet_sameNodeKernel s v).wp (fun x => x = initial)
  have hf := fun id => (freeNode_sameNodeKernel id).wp (fun x => x = initial)
  mvcgen [WG.AllowedIps.removeParentTail, hn, hs, hslot, hf, branch]

theorem removeNodeBody_sameNodeKernel (id : NodeId) :
    SameNodeKernel (WG.AllowedIps.removeNodeBody id) := by
  apply SameView.of_wp
  intro initial
  have hn := fun id => (SameView.of_sameKernel nodeKernel (getNode_sameKernel id)).wp (fun x => x = initial)
  have hb := fun n i => (SameView.of_sameKernel nodeKernel (aipBitAt_sameKernel n i)).wp (fun x => x = initial)
  have hs := fun id n => (setNode_sameNodeKernel id n).wp (fun x => x = initial)
  have hslot := fun s v => (slotSet_sameNodeKernel s v).wp (fun x => x = initial)
  have hf := fun id => (freeNode_sameNodeKernel id).wp (fun x => x = initial)
  have ht := fun p s => (removeParentTail_sameNodeKernel p s).wp (fun x => x = initial)
  mvcgen [WG.AllowedIps.removeNodeBody, hn, hb, hs, hslot, hf, ht, branch, invariant]

end Leanux.Proofs.Framing
