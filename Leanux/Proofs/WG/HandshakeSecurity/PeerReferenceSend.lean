import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceEnvWorkers
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeSend

/-! Queued and directly drained sends certify their actual exchange entries. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

private theorem saved_native (p : Peer) (action : WG.M α) (safe : Framing.Preserves Inv action) :
    StatePrefixPreserves (fun h w _ => Saved.Saved p h w) (Safe (E := E)) (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1.1)
  intro h w a x v b before run
  exact ⟨⟨before.1.1,(hoare_iff_run_ambient _ _ _).mp safe w a x v b before.1.2 run⟩,before.2⟩

private theorem update_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WGPrefix E α)
    (same : ∀ p, (f p).refcount = p.refcount) (tail : ∀ u, Observed (E := E) (next u)) :
    Observed (E := E) (liftWGPrefix (getPeer pid) >>= fun p => liftWGPrefix (setPeer pid (f p)) >>= next) :=
  StatePrefixEnsures.bind (Saved.read_saved pid) (fun p =>
    StatePrefixEnsures.bind (Saved.write_saved pid p f same) tail)

macro "peer_reference_send_step" : tactic => `(tactic| first
  | unfold Observed
  | (nonce_source_head getPeer; exact lift _ (read_peer _))
  | (nonce_source_head branchExpired; exact lift _ (world (branchExpired_sameWGWorld _ _ _ _)))
  | (nonce_source_head addMacToPacket; exact lift _ (mac _ _))
  | (nonce_source_head timersTraversal; exact lift _ (traversal _))
  | (nonce_source_head timersAnyAuthenticatedPacketSent; exact lift _ (sent _))
  | (nonce_source_head timersHandshakeInitiated; exact lift _ (initiated _))
  | (nonce_source_head sendBufferToPeer; exact lift _ (send_buffer _ _))
  | (first | nonce_source_head branch | nonce_source_head hiddenClock64 | nonce_source_head hidden | nonce_source_head invariant
     exact ambient _)
  | (exchange_update_cut; apply update_bind; first | intro p; rfl | intro u)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | (nonce_source_head Pure.pure; exact pure _)
  | split
  | (with_reducible intro x; try dsimp only))

theorem send_observed (pid : PeerId) : Observed (E := E) (SendExchange.sendWith EntrySource.sendOps pid) := by
  change StatePrefixPreserves (fun h w _ => StateInv (E := E) h w) (Safe (E := E)) _
  unfold SendExchange.sendWith
  simp only [EntrySource.sendOps]
  repeat' first
    | (nonce_source_head EntrySource.createInitiation; exact create_initiation_observed _)
    | peer_reference_send_step

theorem worker_observed (pid : PeerId) : Observed (E := E) (SendExchange.workerWith EntrySource.sendOps pid) := by
  unfold SendExchange.workerWith
  exact StatePrefixEnsures.bind (send_observed pid) (fun _ => lift _ (peer_put _))

theorem after_take_observed (pid : PeerId) :
    Observed (E := E) (SendExchange.afterTakeWith (fun {_} action => liftWGPrefix action)
      (SendExchange.workerWith EntrySource.sendOps) pid) := by
  unfold SendExchange.afterTakeWith
  apply StatePrefixEnsures.bind (Saved.read_saved pid)
  intro p
  dsimp only
  split
  · apply StatePrefixEnsures.bind (saved_native p _ (hoare_liftAmbient (AmbientM.invariant _) _))
    intro _
    apply StatePrefixEnsures.bind (saved_native p getDev (store getDev_sameWGStore))
    intro d
    apply StatePrefixEnsures.bind (Saved.write_saved pid p
      (fun q => {q with handshakePending := d.sendWorkQueue.contains pid}) (fun _ => rfl))
    intro _
    repeat' first
      | (nonce_source_head SendExchange.workerWith; exact worker_observed pid)
      | peer_reference_send_step
  · apply StatePrefixEnsures.bind (saved_native p getDev (store getDev_sameWGStore))
    intro d
    apply StatePrefixEnsures.bind (Saved.write_saved pid p
      (fun q => {q with handshakePending := d.sendWorkQueue.contains pid}) (fun _ => rfl))
    intro _
    repeat' first
      | (nonce_source_head SendExchange.workerWith; exact worker_observed pid)
      | peer_reference_send_step

theorem flushed_observed (pid : PeerId) : Observed (E := E) (EntrySource.flushed pid) := by
  unfold EntrySource.flushed SendExchange.flushedWith
  exact StatePrefixEnsures.bind (lift _ (modify_device _ (fun _ => rfl)))
    (fun _ => after_take_observed pid)

theorem send_one : ProductPreserves (E := E) (Driver.sendWorkerObserved EntrySource.hooks (E := E)) := by
  unfold Driver.sendWorkerObserved SendExchange.oneWith
  apply PrefixPreserves.bind
  · apply product_lift
    apply (hoare_iff_run _ _ _).mpr
    intro w value v before run
    rw [(AuthenticatedEffects.SendWorkCauses.select_member w v value run).1]
    exact before
  · intro pid
    exact product_safe (flushed_observed pid)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
