import Leanux.Proofs.WG.Noise.PendingTicketHandshakeFrames
import Leanux.Proofs.WG.Noise.PendingTicketTimerFrames
import Leanux.Proofs.WG.Config.PeerDead
import Leanux.Proofs.Framing.WGDump

/-! Pending tickets project the landed allowed-IP list/node store frames.
The removal loop uses the existing original source factor and generic finite
loop rule; no trie walk, lookup proof, or shape invariant is duplicated. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing

theorem listDel_frame (id : NodeId) : SameView view (listDel id) :=
  frame_from_fields (CurrentSlots.Removal.listDel_fields id)
    (Keypairs.WGFrames.listDel_sameSnapshot id)

theorem free_frame : SameView view WG.free :=
  frame_from_fields CurrentSlots.Removal.free_fields Keypairs.WGFrames.free_sameSnapshot

theorem frame_node {α : Type} (action : WG.M α) (frame : SameNode action) :
    SameView view action := by
  apply frame.of_factor storeView view
  intro w
  simp [storeView,nodeView,nodeDevice,wgStoreView,view,pending,Option.bind_map,Function.comp_def]

private theorem peerRead_pending (pid : PeerId) : SameView view (getPeer pid) := by
  intro initial
  exact hoare_consequence (getPeer_spec pid (fun w => view w = initial))
    (fun _ h => h) (fun _ _ h => h.1)

/-- Whole original allowed-IP removal preserves pending allocation identities,
including arbitrary malformed trie states whenever the operation returns. -/
theorem removeByPeer_frame (pid : PeerId) : SameView view (removeByPeer pid) := by
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep
  apply (peerRead_pending pid).bind
  intro p
  apply (frame_ambient (AmbientM.branch .removeListEmpty p.allowedipsList.isEmpty)).bind
  intro empty
  cases empty with
  | true => exact SameView.pure view ()
  | false =>
    apply (modifyDev_frame
      (fun d => {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq+1}})
      (fun _ => rfl) (fun _ => rfl)).bind
    intro u
    apply (DumpComposition.forIn_sameView p.allowedipsList ()
      (fun id _ => AllowedIps.removeStep id) (fun id _ => ?_)).bind
    · intro u
      exact frame_ambient (AmbientM.branch .removeListIter false)
    · unfold AllowedIps.removeStep
      exact (frame_ambient (AmbientM.branch .removeListIter true)).bind (fun _ =>
        (listDel_frame id).bind (fun _ =>
          frame_node _ (removeNodeBody_sameNode id)))

theorem makeDeadAfterRemoval_frame (pid : PeerId) :
    SameView view (Config.makeDeadAfterRemoval pid) := by
  have modify_eq (f : Peer → Peer) : modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have factor : Config.makeDeadAfterRemoval pid = (do
      let d ← getDev
      _ ← branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid))
      modifyDev fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}
      modifyPeer pid fun p => {p with isDead := true}) := by
    simp only [Config.makeDeadAfterRemoval,modify_eq]
  rw [factor]
  have read : SameView view getDev := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient d v after run
    cases device : w.dev with
    | none =>
      simp [getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some device =>
      simp [getDev,device] at run
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      rfl
  exact read.bind (fun d =>
    (frame_ambient (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid)))).bind (fun _ =>
    (modifyDev_frame (fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)})
      (fun _ => rfl) (fun _ => rfl)).bind (fun _ =>
      modifyPeer_spec_pending_variant pid (fun p => {p with isDead := true}) (fun _ => rfl))))

/-- Unlisting and dead-marking do not clear or install pending slots. The
original allowed-IP removal may stop and requires no shape premise here. -/
theorem peerMakeDead_frame (pid : PeerId) : SameView view (peerMakeDead pid) := by
  rw [Config.peerMakeDead_source]
  exact (modifyDev_frame (Config.unlistPeer · pid) (fun _ => rfl) (fun _ => rfl)).bind (fun _ =>
    (removeByPeer_frame pid).bind (fun _ => makeDeadAfterRemoval_frame pid))

end Leanux.Proofs.WG.Noise.PendingTickets
