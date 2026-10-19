import Leanux.Proofs.WG.TransmitSecurity.StagedSavedFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedExactFrames

/-! The selected batch stays outside the staged queue until the native arm
restores it or allocates its packets. Reference and nonce operations preserve
that temporary empty queue and the saved source positions. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal

theorem Native.key_put (kid : Option KeypairId) (now : Bool) :
    Preserves (Inv h) (keypairPut kid now) :=
  frame (PacketOrigins.epoch_ring (TxRing.keypairPut_frame kid now))
    (Staged.of_view _ (Exact.key_put kid now))

theorem Native.peer_get (pid : PeerId) : Preserves (Inv h) (peerGet pid) :=
  frame (PacketOrigins.epoch_ring (TxRing.peerGet_frame pid)) (Staged.of_view _ (Exact.peer_get pid))

theorem Native.write_key (kid : KeypairId) (key : Keypair) :
    Preserves (Inv h) (setKeypair kid key) :=
  Native.modify_device _ (fun _ => rfl) (fun _ => rfl)

theorem key_write_epoch (kid : KeypairId) (key : Keypair) : SameView Packets.epoch (setKeypair kid key) :=
  PacketOrigins.epoch_ring (TxRing.modify _ (fun _ => rfl) (fun _ => rfl))

theorem held_lift (action : WG.M α) (native : ∀ h, Preserves (Inv h) action)
    (epoch : SameView Packets.epoch action) (queues : SameView stagedAt action) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix action) :=
  (state_lift action native).saved (erasesStatePrefix_lift _) epoch queues

theorem held_read_peer (target : PeerId) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (getPeer target)) :=
  held_lift _ (fun _ => Native.read_peer target)
    (PacketOrigins.epoch_ring (TxRing.getPeer_frame target)) (Exact.read_peer target)

theorem held_read_key (kid : KeypairId) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (getKeypair kid)) :=
  held_lift _ (fun _ => Native.read_key kid)
    (PacketOrigins.epoch_ring (TxRing.getKeypair_frame kid)) (Exact.read_key kid)

theorem held_write_key (kid : KeypairId) (key : Keypair) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (setKeypair kid key)) :=
  held_lift _ (fun _ => Native.write_key kid key) (key_write_epoch kid key) (set_key_staged kid key)

theorem held_key_put (kid : Option KeypairId) (now : Bool) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (keypairPut kid now)) :=
  held_lift _ (fun _ => Native.key_put kid now)
    (PacketOrigins.epoch_ring (TxRing.keypairPut_frame kid now)) (Exact.key_put kid now)

theorem held_peer_get (target : PeerId) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (peerGet target)) :=
  held_lift _ (fun _ => Native.peer_get target)
    (PacketOrigins.epoch_ring (TxRing.peerGet_frame target)) (Exact.peer_get target)

theorem held_ambient (action : AmbientM α) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix (monadLift action : WG.M α)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1.2)
  intro h w a value v b before run
  exact (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient action (fun w => Held pid peer h w a))
    w a value v b before run

theorem held_world (action : WG.M α) (unchanged : SameView id action) :
    StatePrefixPreserves (Held pid peer) Safe (liftWGPrefix action) :=
  held_lift action (fun _ => unchanged.wp (Inv _))
    (unchanged.factor Packets.epoch) (unchanged.factor stagedAt)

theorem held_restore (pid : PeerId) (peer : Peer) :
    StatePrefixEnsures (Held pid peer) Safe
      (liftWGPrefix (HandshakeSecurity.NonceRejection.restore pid peer.staged))
      (fun _ h w _ => Carrier h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1.2)
  intro h w a value v b before run
  exact ⟨restore_origin pid peer ⟨value,w,v,a,b⟩ run before.1.1 before.2,before.1.2⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
