import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPeerReleaseSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPublicationFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReleaseCarrier

/-! Native validity and independent history frames for the existing nested
peer-release cut. The suffix consists only of its real peer access events. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations
set_option pp.structureInstances false

theorem ops_erases : PeerSource.Ops.Erases ops where
  step := fun _ => focusStatePrefix_erases _ _ (erasesStatePrefix_lift _)
  read := fun pid => focusStatePrefix_erases _ _ (Peers.getPeerPrefix_erases pid)
  write := fun pid p => focusStatePrefix_erases _ _ (Peers.setPeerPrefix_erases pid p)
  erase := fun pid n => focusStatePrefix_erases _ _ (Peers.erasePeerPrefix_erases pid n)

theorem cut_erases (peer : Option PeerId) : ErasesStatePrefix (cut peer) (releaseCut peer) :=
  PeerSource.cut_erases ops_erases peer

theorem cut_valid (peer : Option PeerId)
    (performed : runWGPrefix (cut peer) w a history = (.ok ((value,v),b),last)) :
    (⟨value,w,v,a,b⟩ : WGRunWitness _).Valid (releaseCut peer) := by
  have native := cut_erases peer w a history
  change (runWGPrefix (cut peer) w a history).1 = _ at native
  rw [performed] at native
  exact native.symm

theorem cut_history (peer : Option PeerId) (w : WGWorld) (a : Ambient)
    (history : List CausalJournal.Event) :
    ∃ events : List Peers.PeerEvent,
      (runWGPrefix (cut peer) w a history).2 =
        history ++ events.map (TxSource.peerEncode CausalJournal.txEvent) := by
  have focused := PeerSource.cut_focus (TxSource.peerEncode CausalJournal.txEvent)
    (TxSource.peerDecode CausalJournal.txEvent?) (fun _ => rfl)
    PeerSource.peers PeerSource.peers_appends peer
  unfold cut ops
  rw [focused]
  exact ⟨_,rfl⟩

theorem cut_birth_quiet (peer : Option PeerId) (w : WGWorld) (a : Ambient)
    (history : List CausalJournal.Event) :
    ∃ suffix, (runWGPrefix (cut peer) w a history).2 = history ++ suffix ∧
      ∀ event ∈ suffix, birthPackets event = [] := by
  obtain ⟨events,same⟩ := cut_history peer w a history
  refine ⟨_,same,?_⟩
  intro event member
  obtain ⟨prior,_,rfl⟩ := List.mem_map.mp member
  rfl

theorem finish_native (value : Option (PeerId × Peer)) :
    finish value = liftPrefix (liftWG (match value with
      | none => pure ()
      | some (pid,p) => releaseFinish pid p)) := by
  cases value with
  | none => rfl
  | some pair =>
    obtain ⟨pid,p⟩ := pair
    change liftWGObserver (focusStatePrefix (TxSource.peerEncode CausalJournal.txEvent)
      (TxSource.peerDecode CausalJournal.txEvent?) (liftWGPrefix (releaseFinish pid p))) = _
    rw [CompletionEffects.lift_focus,liftWGObserver_lift]
    funext w history
    change ((liftWG (releaseFinish pid p)).run w,history ++
      ((history.filterMap (TxSource.peerDecode CausalJournal.txEvent?)).drop
        (history.filterMap (TxSource.peerDecode CausalJournal.txEvent?)).length).map
        (TxSource.peerEncode CausalJournal.txEvent)) = _
    simp only [List.drop_length,List.map_nil,List.append_nil]
    rfl

theorem finish_appends (value : Option (PeerId × Peer)) : Appends (finish value) := by
  rw [finish_native]
  exact Appends.lift _

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
