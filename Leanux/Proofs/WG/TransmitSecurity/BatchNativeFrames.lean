import Leanux.Proofs.WG.TransmitSecurity.BatchCoherenceFrames
import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceDisposal
import Leanux.Proofs.WG.RetirementSecurity.ReceiveOccurrenceFrames

/-! Native leaf frames for queued-batch peer/key homogeneity. Final releases
may erase queues or packets; the survivor relation is explicit. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

theorem payment {action : WG.M α}
    (queueFrame : ∀ initial, Preserves (DurableHolders.Frame initial) action)
    (material : SameView PacketMaterial.view action) : Preserves Inv action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have queues := (hoare_iff_run_ambient _ _ _).mp (queueFrame w) w a result v b
    (DurableHolders.Frame.refl w) run
  have cells := (ProjectedAction.iff_run_ambient _ _ _).mp material w a result v b run
  apply before.transport
  · intro pid p found items member
    have old := queues.tx pid p.txQueue.all (by
      simpa [handoffTxView,peerAt] using congrArg (Option.map (fun p => p.txQueue.all)) found)
    obtain ⟨q,resident,queue⟩ := Option.map_eq_some_iff.mp old
    exact ⟨q,resident,queue.symm ▸ member⟩
  · intro id packet resident
    have cell := congrFun cells id
    simp only [PacketMaterial.view,resident,Option.map_some] at cell
    obtain ⟨old,found,equal⟩ := Option.map_eq_some_iff.mp cell.symm
    exact ⟨old,found,equal.symm⟩

theorem key_put (kid : Option KeypairId) (now : Bool) : Preserves Inv (keypairPut kid now) :=
  payment (HolderWorkFrames.keypairPut_frame kid now)
    (PacketMaterial.of_packets (TxDisposition.keyPut_packets kid now))

theorem peer_put (pid : Option PeerId) : Preserves Inv (peerPut pid) :=
  payment (HolderWorkFrames.peerPut_frame pid)
    (PacketMaterial.of_packets (TxDisposition.peerPut_packets pid))

theorem key_get (kid : Option KeypairId) : Preserves Inv (keypairGet kid) :=
  frame (pair (keyGet_tx_queues kid) (PacketMaterial.of_packets ((keyGet_cryptWire kid).factor Prod.snd)))

theorem read_peer (pid : PeerId) : Preserves Inv (getPeer pid) := getPeer_preserves pid Inv

theorem read_key (kid : KeypairId) : Preserves Inv (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (KeyTimes.getKeypair_return kid w v result a b run).1 ▸ before

theorem read_packet (id : SkbId) : Preserves Inv (getTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (Packets.getTxSkb_current id w v result a b run).1 ▸ before

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves Inv action :=
  frame (same.of_factor (fun s => view {dev := s.dev}) view (fun _ => rfl))

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
