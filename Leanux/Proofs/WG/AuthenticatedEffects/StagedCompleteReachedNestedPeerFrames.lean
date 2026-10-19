import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNestedPeerSource

/-! Exact erasure and history frames for the nested pre-erasure stages.
The native projection is the existing release stage; the actual history
contains only its original peer access records. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NestedPeer
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open HandshakeSecurity.StagedDisposal PeerRetirement
set_option maxHeartbeats 800000

theorem native_prefix (stage : Stage) (peer : Option PeerId) :
    prefixAt PeerSource.native stage peer=stage.prefix peer := by
  cases stage <;> rfl

theorem prefix_erases {o : PeerSource.Ops (WGPrefix E)} (h : PeerSource.Ops.Erases o)
    (stage : Stage) (peer : Option PeerId) :
    ErasesStatePrefix (prefixAt o stage peer) (stage.prefix peer) := by
  rw [←native_prefix]
  cases stage <;> cases peer <;>
    simp only [prefixAt,checkedTo,unlinkTo,testTo,decrementTo,readWith,testWith,guardWith,PeerSource.native,id]
  all_goals repeat' disposal_peer_erase h

private def Aligned (encode : E → F) (decode : F → Option E)
    (g : WGPrefix F α) (t : WGPrefix E α) : Prop :=
  StateAppends t ∧ g=focusStatePrefix encode decode t

theorem prefix_focus (encode : E → F) (decode : F → Option E) (inverse : ∀ e,decode (encode e)=some e)
    (o : PeerSource.Ops (WGPrefix E)) (h : PeerSource.Ops.Appends o)
    (stage : Stage) (peer : Option PeerId) :
    StateAppends (prefixAt o stage peer) ∧
      prefixAt (PeerSource.Ops.focus encode decode o) stage peer=
        focusStatePrefix encode decode (prefixAt o stage peer) := by
  change Aligned encode decode (prefixAt (PeerSource.Ops.focus encode decode o) stage peer)
    (prefixAt o stage peer)
  cases stage <;> cases peer <;>
    simp only [prefixAt,checkedTo,unlinkTo,testTo,decrementTo,readWith,testWith,guardWith,PeerSource.Ops.focus]
  all_goals repeat' disposal_peer_align encode decode inverse h

theorem prefix_history (stage : Stage) (peer : Option PeerId) (w : WGWorld) (a : Ambient)
    (history : List CausalJournal.Event) :
    ∃events : List Peers.PeerEvent,(runWGPrefix (prefixAt actual stage peer) w a history).2=
      history++events.map (TxSource.peerEncode CausalJournal.txEvent) := by
  have focused:=(prefix_focus (TxSource.peerEncode CausalJournal.txEvent)
    (TxSource.peerDecode CausalJournal.txEvent?) (fun _=>rfl)
    PeerSource.peers PeerSource.peers_appends stage peer).2
  unfold actual AllocatedObligation.PeerRelease.ops
  rw [focused]
  exact ⟨_,rfl⟩

/-- A completed original pre-erasure stage keeps the same packet projection
and extends its history only with actual quiet access records. -/
theorem stage_accounted (before : CompleteCarrier.Accounted history ledger debts locals w)
    (performed : runWGPrefix (prefixAt actual stage peer) w a history=(.ok ((value,v),b),last)) :
    CompleteCarrier.Accounted last ledger debts locals v := by
  have erased:=prefix_erases AllocatedObligation.PeerRelease.ops_erases stage peer w a history
  change (runWGPrefix (prefixAt actual stage peer) w a history).1=_ at erased
  rw [performed] at erased
  have view:=PeerRetirement.Points.Stage.view erased.symm
  obtain ⟨events,grown⟩:=prefix_history stage peer w a history
  rw [performed] at grown
  change last=history++events.map (TxSource.peerEncode CausalJournal.txEvent) at grown
  rw [grown]
  apply (before.append_quiet _ ?_ ?_).same_view view
  · intro event member
    obtain ⟨prior,_,rfl⟩:=List.mem_map.mp member
    rfl
  · intro event member
    obtain ⟨prior,_,rfl⟩:=List.mem_map.mp member
    exact StagedTerminalComplete.Source.peer_access_quiet prior

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NestedPeer
