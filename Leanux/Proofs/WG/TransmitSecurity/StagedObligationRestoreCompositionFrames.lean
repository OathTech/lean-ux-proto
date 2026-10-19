import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreEntryContracts
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTake
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestore

/-! The same selected tickets survive the native checks and actual reservation
observer. This carrier adds no births and does not assume conservation of a run. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreComposition
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Staged.Origins AuthenticatedEffects.CausalJournal
open HandshakeSecurity.StagedConservation

structure Held (ledger : Ledger) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (history : List Event) (w : WGWorld) (_ : Ambient) : Prop where
  queues : QueueInv history ledger w
  vacant : RestoreEntry.Vacant generation pid peer.internalId w
  aligned : Aligned (Born history generation pid peer.internalId)
    (pendingAt (.selected position) ledger) peer.staged

theorem Held.views_append (before : Held ledger generation pid peer position history w a)
    (suffix : List Event) (epoch : Packets.epoch v = Packets.epoch w)
    (queues : stagedAt v = stagedAt w) :
    Held ledger generation pid peer position (history ++ suffix) v b :=
  ⟨before.queues.views_append suffix epoch queues,before.vacant.views epoch queues,
    before.aligned.history_append suffix⟩

/-- Native erasure is used only for the exact state frame. The observed history
is retained and the original ticket-to-packet alignment is extended to it. -/
theorem held_observed {action : WGPrefix Event α} {native : WG.M α}
    (appends : StateAppends action) (erases : ErasesStatePrefix action native)
    (epoch : SameView Packets.epoch native) (queues : SameView stagedAt native) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True) action := by
  intro w a h before
  obtain ⟨suffix,extended⟩ := appends w a h
  refine ⟨suffix,extended,True.intro,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have run : (native.run w).run a = .ok ((value,v),b) := (erases w a h).symm.trans outcome
    rw [extended]
    exact before.views_append suffix
      ((ProjectedAction.iff_run_ambient _ _ _).mp epoch w a value v b run)
      ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a value v b run)

theorem held_lift (action : WG.M α) (epoch : SameView Packets.epoch action)
    (queues : SameView stagedAt action) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True) (liftWGPrefix action) :=
  held_observed (StateAppends.lift _) (erasesStatePrefix_lift _) epoch queues

theorem held_world (action : WG.M α) (same : SameView id action) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True) (liftWGPrefix action) :=
  held_lift action (same.factor Packets.epoch) (same.factor stagedAt)

theorem held_ambient (action : AmbientM α) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True)
      (liftWGPrefix (monadLift action : WG.M α)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ _ => True.intro)
  intro h w a value v b before run
  have kept := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient action (fun w => Held ledger generation pid peer position h w a))
    w a value v b before run
  exact ⟨kept.queues,kept.vacant,kept.aligned⟩

theorem held_read_key (kid : KeypairId) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True) (liftWGPrefix (getKeypair kid)) :=
  held_lift _ (PacketOrigins.epoch_ring (TxRing.getKeypair_frame kid)) (Exact.read_key kid)

theorem held_write_key (kid : KeypairId) (key : Keypair) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True) (liftWGPrefix (setKeypair kid key)) :=
  held_lift _ (key_write_epoch kid key) (set_key_staged kid key)

theorem held_key_put (kid : Option KeypairId) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True) (liftWGPrefix (keypairPut kid false)) :=
  held_lift _ (PacketOrigins.epoch_ring (TxRing.keypairPut_frame kid false)) (Exact.key_put kid false)

theorem held_key_get (kid : Option KeypairId) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True) (liftWGPrefix (keypairGet kid)) :=
  held_lift _ (PacketOrigins.epoch_ring ((RetirementSecurity.keyGet_cryptWire kid).factor Prod.fst))
    (key_get_staged kid)

theorem held_pure (value : α) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True) (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ _ => True.intro) (fun _ _ _ before => before)

theorem held_emit (event : Event) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True)
      (emitStatePrefix event) :=
  StatePrefixEnsures.emit event (fun _ _ _ _ => True.intro)
    (fun _ _ _ before => before.views_append [event] rfl rfl)

/-- This is the reservation observer used by the final causal source: the
nonce event and completed reservation receipt are both retained. Its actual
native increment preserves the selected ticket list and empty destination. -/
theorem reservation_held (kid : KeypairId) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True)
      (state (Journal.reserve kid)) := by
  apply held_observed (StateAppends.focus _ _ _)
    (focusStatePrefix_erases _ _
      (receiptWGObserved_erases (focusStatePrefix_erases _ _ (Nonce.reserveObserved_erases kid)) _))
    (reserve_epoch kid) (reserve_staged kid)

theorem prefix_held (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True)
      (RestoreEntry.prefixWith liftWGPrefix packets keypair invalid) := by
  have tail (kp : Option KeypairId) :
      StatePrefixPreserves (Held ledger generation pid peer position) (fun _ => True) (do
        liftWGPrefix (keypairPut kp false)
        for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
        _ ← liftWGPrefix (branch .stagedOrphanWalk false)) := by
    apply StatePrefixEnsures.bind (held_key_put kp)
    intro _
    apply StatePrefixEnsures.bind
    · apply StatePrefixEnsures.forInInvariant packets PUnit.unit _
        (fun _ => Held ledger generation pid peer position) (fun _ => True)
        (fun _ _ _ _ _ => True.intro)
      intro packet acc
      exact StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedOrphanWalk true))
        (fun _ => held_pure _)
    · intro _
      exact StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedOrphanWalk false))
        (fun _ => held_pure _)
  unfold RestoreEntry.prefixWith
  dsimp only
  split
  · split
    · apply StatePrefixEnsures.bind (held_read_key _)
      intro key
      exact StatePrefixEnsures.bind (held_write_key _ _) (fun _ => tail _)
    · exact StatePrefixEnsures.bind (held_ambient (AmbientM.invariant "unreachable"))
        (fun _ => tail _)
  · exact tail _

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreComposition
