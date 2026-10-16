import Leanux.Proofs.Framing.WGAllowedIps

/-! Native insertion leaves. Allocating an AipStore object cannot affect the
resident peer, keypair or packet stores; that old structural frame is absent.
The arbitrary device-modifier contract retains its original mask premise. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def nodeAllocationDevice (d : Device) : Device := {nodeDevice d with nextNode := 0}
def nodeAllocationView (g : WGWorld) : WGStoreView :=
  {wgStoreView g with dev := g.dev.map nodeAllocationDevice}
abbrev SameNodeAllocation (a : WG.M α) := SameView nodeAllocationView a

theorem modifyDev_nodeAllocation_spec (P : WGStoreView → Prop) (f : Device → Device)
    (hf : ∀ d, nodeAllocationDevice (f d) = nodeAllocationDevice d) :
    ⦃fun w => ⌜P (nodeAllocationView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (nodeAllocationView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [nodeAllocationView, wgStoreView, modifyDev, Option.map_map, Function.comp_def, hf] using hp

theorem nodePlacement_sameAipStore (trie : Option NodeId) (key cidr bits : Nat) :
    SameView (fun s : AipStore => s) (nodePlacement trie key cidr bits) := by
  apply SameView.of_wp
  intro initial
  have hn := fun node => (getNode_sameAipStore node).wp (fun s => s = initial)
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun s : AipStore => ⌜s = initial⌝⦄ (MonadLift.monadLift a : AipM α)
      ⦃⇓? _ s => ⌜s = initial⌝⦄ := hoare_liftAmbient a _
  mvcgen [-Std.Do.Spec.monadLift_StateT, nodePlacement, hn, AipNode.bitAt, choose,
    prefixMatches, commonBits, branch, branchCmp, invariant, ha]
  all_goals try exact ((⇓? _ s => ⌜s = initial⌝) :
    PostCond _ (.arg AipStore (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem connectNode_sameNextNode (slot : Slot) (node : NodeId) :
    SameView AipStore.nextNode (connectNode slot node) := by
  unfold connectNode
  exact SameView.bind ((getNode_sameAipStore node).factor AipStore.nextNode) (fun n =>
    SameView.bind (setNode_sameNextNode node {n with parent := slot}) (fun _ =>
      slotSet_sameNextNode slot (some node)))

theorem chooseAndConnectNode_sameNextNode (parent node : NodeId) :
    SameView AipStore.nextNode (chooseAndConnectNode parent node) := by
  apply SameView.of_wp
  intro initial
  have hn := fun node => ((getNode_sameAipStore node).factor AipStore.nextNode).wp (fun s => s = initial)
  have hf := fun slot node => (connectNode_sameNextNode slot node).wp (fun s => s = initial)
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun s : AipStore => ⌜s.nextNode = initial⌝⦄ (MonadLift.monadLift a : AipM α)
      ⦃⇓? _ s => ⌜s.nextNode = initial⌝⦄ := hoare_liftAmbient a _
  mvcgen [-Std.Do.Spec.monadLift_StateT, chooseAndConnectNode, choose, invariant, hn, hf, ha]

end Leanux.Proofs.Framing
