import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketMetadataCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReceiveHelperCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRxAccessCanonical

/-! Fixed NAPI helper source trees retain peer reads, RX-queue metadata
writes, packet-store adapters and key-reference operations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NapiMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def pendingShape : PeerMetadata.Shape RxNapi.pendingSource := by
  unfold RxNapi.pendingSource
  repeat' receive_metadata_step

noncomputable def scheduledShape : PeerMetadata.Shape RxNapi.scheduledSource := by
  unfold RxNapi.scheduledSource
  repeat' receive_metadata_step

noncomputable def peekShape (pid : PeerId) :
    PeerMetadata.Shape (do (← getPeer pid).rxQueue.peek) := by
  repeat' receive_metadata_step

noncomputable def installShape (pid : PeerId) (queue : PrevQueue SkbId) :
    PeerMetadata.Shape (do setPeer pid {(← getPeer pid) with rxQueue:=queue}) :=
  PeerMetadata.updateShape pid _ (fun _ => ⟨rfl,rfl,rfl⟩)

noncomputable def writePeerShape (pid : PeerId) (queue : Peer → PrevQueue SkbId)
    (scheduled : Peer → Bool) : PeerMetadata.Shape (do
      let peer ← getPeer pid
      setPeer pid {peer with rxQueue:=queue peer,napiScheduled:=scheduled peer}) :=
  PeerMetadata.updateShape pid _ (fun _ => ⟨rfl,rfl,rfl⟩)

noncomputable def dropShape (pid : PeerId) : PeerMetadata.Shape (do
    setPeer pid {(← getPeer pid) with rxQueue:=(← getPeer pid).rxQueue.dropPeeked}) := by
  apply PeerMetadata.Shape.saved
  intro saved
  simp only [getPeer,getDev,invariant]
  repeat' saved_peer_source_step

noncomputable def endpointShape (source : SkbSource) : PeerMetadata.Shape (endpointFromSkb source) := by
  unfold endpointFromSkb
  repeat' receive_metadata_step

noncomputable def keyPutShape (kid : KeypairId) : PeerMetadata.Shape (keypairPut (some kid) false) :=
  .access (Access.putShape _ _)

noncomputable def completeShape (pid : PeerId) :
    PeerMetadata.Shape (do setPeer pid {(← getPeer pid) with napiScheduled:=false}) :=
  PeerMetadata.updateShape pid _ (fun _ => ⟨rfl,rfl,rfl⟩)

noncomputable def readyShape (first : Option SkbId) : RxAccess.Shape (WG.andM (branch .rxPollPacket first.isSome) do
    let some id := first | invariant "unreachable"
    branch .rxPollNotUncrypted ((← getRxSkb id).state != .uncrypted)) := by
  unfold WG.andM
  repeat' rx_access_source_step

noncomputable def packetShape (skb : SkbId) : RxAccess.Shape (getRxSkb skb) :=
  .skb _ (CompletePollNative.get_rx skb)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NapiMetadata
