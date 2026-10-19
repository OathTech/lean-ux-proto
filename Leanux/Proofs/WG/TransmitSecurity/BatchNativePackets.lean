import Leanux.Proofs.WG.TransmitSecurity.BatchNativeAllocation

/-! Queue-preserving packet edits and disposal retain homogeneous batches.
The projection permits bytes and marks to change while retaining peer/key words. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

theorem queues_retains (before : Inv w) (queues : handoffTxView v = handoffTxView w)
    (packets : ∀ id packet, TxDisposition.txPackets v id = some packet →
      ∃ old, TxDisposition.txPackets w id = some old ∧
        PacketMaterial.material packet = PacketMaterial.material old) : Inv v := by
  apply before.transport ?_ packets
  intro pid p found items member
  have current : handoffTxView v pid = some p.txQueue.all := by
    simpa [handoffTxView,peerAt] using congrArg (Option.map (fun p => p.txQueue.all)) found
  rw [queues] at current
  obtain ⟨old,resident,queue⟩ := Option.map_eq_some_iff.mp current
  exact ⟨old,resident,queue.symm ▸ member⟩

theorem write_packet (id : SkbId) (f : DataPacket → DataPacket)
    (same : ∀ p, PacketMaterial.material (f p) = PacketMaterial.material p) :
    Preserves Inv (setTxSkb id f) :=
  frame (pair (ReceiveOccurrences.skb_queues _) (PacketMaterial.set_tx id f same))

theorem free_packet (id : SkbId) : Preserves Inv (freeTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ReceiveOccurrences.skb_queues (SkbStore.freeTx id)) w a result v b run
  have packets := (hoare_iff_run_ambient _ _ _).mp
    (TxDisposition.free_packet_wp id (TxDisposition.txPackets w)) w a result v b rfl run
  apply queues_retains before queues
  intro target packet resident
  rw [packets] at resident
  by_cases same : id = target
  · simp only [same,ite_true] at resident; cases resident
  · exact ⟨packet,by simpa only [same,ite_false] using resident,rfl⟩

theorem peer_get (pid : PeerId) : Preserves Inv (peerGet pid) :=
  frame (pair (ownership_queues (peerGet_ownership pid))
    (PacketMaterial.of_packets (TxDisposition.peerGet_packets pid)))

theorem no_key (pid : PeerId) (packets : List WG.Packet) (kid : Option KeypairId) (invalid : Bool) :
    Preserves Inv (stagedOutNokey pid packets kid invalid) :=
  wire (noKey_tx_queues pid packets kid invalid) (noKey_cryptWire pid packets kid invalid)

theorem publish (items : List SkbId) (state : PacketState) :
    Preserves Inv (enqueuePerPeerTx items state) := by
  apply frame (pair ?_ (PacketMaterial.publish items state))
  exact (TxDisposition.publication_queues items state).of_factor
    (fun cells pid => (cells pid).map PrevQueue.all) handoffTxView
    (fun w => by funext pid; simp [handoffTxView,TxDisposition.txQueues,
      PeerBorrow.resident,wgStoreView,Option.map_map,Function.comp_def])

theorem modify_device (f : Device → Device) (peers : ∀ d, (f d).peers = d.peers)
    (packets : ∀ d, (f d).txSkbs = d.txSkbs) : Preserves Inv (modifyDev f) := by
  apply frame (pair ?_ (PacketMaterial.modify_device f packets))
  intro initial
  apply hoare_modify
  intro w before
  change (fun pid => handoffTxView _ pid) = initial
  change (fun pid => handoffTxView w pid) = initial at before
  simpa only [handoffTxView,Option.bind_map,Function.comp_def,peers] using before

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
