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
  have ha {α : Type} (a : AmbientM α) : SameView (fun s : AipStore => s) (monadLift a : AipM α) :=
    fun initial => hoare_liftAmbient a (fun s => s = initial)
  have hc (n : AipNode) (key : Nat) : SameView (fun s : AipStore => s) (choose n key : AipM Nat) := by
    unfold choose
    split
    · exact SameView.bind (ha (AmbientM.invariant "choose on a full-length node"))
        (fun _ => SameView.pure _ _)
    · exact SameView.pure _ _
  have hb (n : AipNode) (bit : Nat) : SameView (fun s : AipStore => s) (n.bitAt bit : AipM (Option NodeId)) := by
    unfold AipNode.bitAt
    split
    · exact SameView.pure _ _
    · exact ha (AmbientM.invariant _)
  have common (n : AipNode) (key bits : Nat) : SameView (fun s : AipStore => s) (commonBits n key bits : AipM Nat) := by
    unfold commonBits
    apply SameView.bind (ha (AmbientM.branch .commonBits32 _))
    intro b32
    split
    · exact SameView.pure _ _
    · apply SameView.bind (ha (AmbientM.branch .commonBits128 _))
      intro b128
      split
      · apply SameView.bind (ha (AmbientM.branch .fls128High _))
        intro high
        split <;> exact SameView.bind (SameView.pure _ _) (fun _ => SameView.pure _ _)
      · exact SameView.pure _ _
  have hp (n : AipNode) (key bits : Nat) : SameView (fun s : AipStore => s) (prefixMatches n key bits : AipM Bool) := by
    unfold prefixMatches
    exact SameView.bind (common n key bits) (fun _ => SameView.pure _ _)
  intro initial
  unfold nodePlacement
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind
  · apply list_view_spec id (fun s => s = initial)
    intro i accumulator
    split
    · exact preserves_bind (ha (AmbientM.branch .placementNode false) initial) (fun _ => preserves_pure _)
    · apply preserves_bind (ha (AmbientM.branch .placementNode true) initial)
      intro _
      simp only [pure_bind]
      apply preserves_bind (getNode_sameAipStore _ initial)
      intro n
      apply preserves_bind (ha (AmbientM.branchCmp .placementCidrLe _ _ _) initial)
      intro bounded
      split
      · exact preserves_pure _
      · apply preserves_bind (hp _ _ _ initial)
        intro matched
        apply preserves_bind (ha (AmbientM.branch .placementPrefixMatches matched) initial)
        intro prefixAccepted
        split
        · exact preserves_pure _
        · apply preserves_bind (ha (AmbientM.branchCmp .placementExact _ _ _) initial)
          intro exactMatch
          split
          · exact preserves_pure _
          · apply preserves_bind (hc _ _ initial)
            intro bit
            exact preserves_bind (hb _ bit initial) (fun _ => preserves_pure _)
  · intro result
    split
    · exact preserves_pure _
    · exact ha (AmbientM.invariant "node_placement deeper than MAX_ALLOWEDIPS_DEPTH") initial

theorem connectNode_sameNextNode (slot : Slot) (node : NodeId) :
    SameView AipStore.nextNode (connectNode slot node) := by
  unfold connectNode
  exact SameView.bind ((getNode_sameAipStore node).factor AipStore.nextNode) (fun n =>
    SameView.bind (setNode_sameNextNode node {n with parent := slot}) (fun _ =>
      slotSet_sameNextNode slot (some node)))

theorem chooseAndConnectNode_sameNextNode (parent node : NodeId) :
    SameView AipStore.nextNode (chooseAndConnectNode parent node) := by
  have hc (n : AipNode) (key : Nat) : SameView AipStore.nextNode (choose n key : AipM Nat) := by
    unfold choose
    split
    · exact SameView.bind
        (fun initial => hoare_liftAmbient (AmbientM.invariant "choose on a full-length node")
          (fun s : AipStore => s.nextNode = initial))
        (fun _ => SameView.pure _ _)
    · exact SameView.pure _ _
  unfold chooseAndConnectNode
  apply SameView.bind ((getNode_sameAipStore parent).factor AipStore.nextNode)
  intro pn
  apply SameView.bind ((getNode_sameAipStore node).factor AipStore.nextNode)
  intro child
  exact SameView.bind (hc pn child.bits) (fun bit => connectNode_sameNextNode (.child parent bit) node)

end Leanux.Proofs.Framing
