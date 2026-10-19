import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueueFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedCreationFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedPeerViewFrames

/-! Native adapters use exact staged projections, never the deletion-retaining
Staged.Frame. Releases which may dispose a staged queue require ledger transfer. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.QueueNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

variable {history : List AuthenticatedEffects.CausalJournal.Event} {ledger : Ledger}

theorem store {action : WG.M α} (same : SameWGStore action) :
    Preserves (QueueInv history ledger) action :=
  queue_frame (same.of_factor (fun s => s.dev.map Device.ifindex) Packets.epoch (fun _ => rfl))
    (Exact.store same)

theorem world {action : WG.M α} (same : SameView id action) :
    Preserves (QueueInv history ledger) action :=
  queue_frame (same.factor Packets.epoch) (same.factor stagedAt)

theorem read_peer (pid : PeerId) : Preserves (QueueInv history ledger) (getPeer pid) :=
  queue_frame (PacketOrigins.epoch_ring (TxRing.getPeer_frame pid)) (Exact.read_peer pid)

theorem read_key (kid : KeypairId) : Preserves (QueueInv history ledger) (getKeypair kid) :=
  queue_frame (PacketOrigins.epoch_ring (TxRing.getKeypair_frame kid)) (Exact.read_key kid)

theorem modify_device (f : Device → Device)
    (epoch : ∀ d, (f d).ifindex = d.ifindex)
    (peers : ∀ d, (f d).peers = d.peers) :
    Preserves (QueueInv history ledger) (modifyDev f) := by
  apply queue_frame ?_ (Exact.modify_device f peers)
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases run
  simp [Packets.epoch,Option.map_map,Function.comp_def,epoch]

theorem modify_world (f : WGWorld → WGWorld)
    (epoch : ∀ w, Packets.epoch (f w) = Packets.epoch w)
    (queues : ∀ w, stagedAt (f w) = stagedAt w) :
    Preserves (QueueInv history ledger) (modify f : WG.M Unit) := by
  apply queue_frame ?_ (Exact.modify_world f queues)
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases run
  exact epoch w

theorem update_peer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    Preserves (QueueInv history ledger) (getPeer pid >>= fun p => setPeer pid (f p)) :=
  queue_frame (SameView.bind (PacketOrigins.epoch_ring (TxRing.getPeer_frame pid))
    (fun p => PacketOrigins.epoch_ring (TxRing.setPeer_frame pid (f p))))
    (Exact.update_peer pid f same)

theorem update_peer_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WG.M α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged)
    (tail : ∀ x, Preserves (QueueInv history ledger) (next x)) :
    Preserves (QueueInv history ledger) (getPeer pid >>= fun p => setPeer pid (f p) >>= next) := by
  simpa only [bind_assoc] using preserves_bind (update_peer pid f same) tail

theorem key_get (kid : Option KeypairId) : Preserves (QueueInv history ledger) (keypairGet kid) :=
  queue_frame (PacketOrigins.epoch_ring ((RetirementSecurity.keyGet_cryptWire kid).factor Prod.fst))
    (Origins.key_get_staged kid)

theorem key_put (kid : Option KeypairId) (now : Bool) :
    Preserves (QueueInv history ledger) (keypairPut kid now) :=
  queue_frame (PacketOrigins.epoch_ring (TxRing.keypairPut_frame kid now)) (Exact.key_put kid now)

theorem peer_get (pid : PeerId) : Preserves (QueueInv history ledger) (peerGet pid) :=
  queue_frame (PacketOrigins.epoch_ring (TxRing.peerGet_frame pid)) (Exact.peer_get pid)

theorem write_key (kid : KeypairId) (key : Keypair) :
    Preserves (QueueInv history ledger) (setKeypair kid key) :=
  queue_frame (Origins.key_write_epoch kid key) (Origins.set_key_staged kid key)

theorem index (action : IndexM α) : Preserves (QueueInv history ledger) (liftIndex action) := by
  apply queue_frame ?_ (Exact.index action)
  intro initial
  apply hoare_liftIndex
  intro w d table before device
  rw [←before]
  simp only [Packets.epoch,device,Option.map_some]

theorem skb (action : SkbM α) : Preserves (QueueInv history ledger) (liftSkb action) :=
  queue_frame (PacketOrigins.skb_epoch action) (Exact.skb action)

theorem reserve (kid : KeypairId) : Preserves (QueueInv history ledger) (Nonce.reserveNative kid) :=
  queue_frame (Origins.reserve_epoch kid) (Origins.reserve_staged kid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.QueueNative
