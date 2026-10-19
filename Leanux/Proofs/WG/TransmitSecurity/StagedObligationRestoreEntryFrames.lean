import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreEntrySource
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTakeFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueueFramesNative

/-! Exact frames between taking and restoring a staged queue. Invalidation,
key repayment and nonce reservation cannot change its allocation or contents. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Staged.Origins HandshakeSecurity.StagedConservation

def Vacant (generation : Nat) (pid : PeerId) (allocation : Nat) (w : WGWorld) : Prop :=
  Packets.epoch w = some generation ∧ stagedAt w pid = some (allocation,[])

def Entry (generation : Nat) (pid : PeerId) (allocation : Nat) (Safe : List E → Prop)
    (h : List E) (w : WGWorld) (_ : Ambient) : Prop :=
  Vacant generation pid allocation w ∧ Safe h

variable {E : Type} {Safe : List E → Prop}

theorem Vacant.views (before : Vacant generation pid allocation w)
    (epoch : Packets.epoch v = Packets.epoch w) (queues : stagedAt v = stagedAt w) :
    Vacant generation pid allocation v := by
  exact ⟨epoch.trans before.1,by rw [queues]; exact before.2⟩

theorem vacant_frame {action : WG.M α} (epoch : SameView Packets.epoch action)
    (queues : SameView stagedAt action) : Preserves (Vacant generation pid allocation) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  exact before.views
    ((ProjectedAction.iff_run_ambient _ _ _).mp epoch w a value v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a value v b run)

theorem entry_lift (action : WG.M α) (epoch : SameView Packets.epoch action)
    (queues : SameView stagedAt action) :
    StatePrefixPreserves (Entry generation pid allocation Safe) Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.2)
  intro h w a value v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (vacant_frame epoch queues)
    w a value v b before.1 run,before.2⟩

theorem entry_world (action : WG.M α) (same : SameView id action) :
    StatePrefixPreserves (Entry generation pid allocation Safe) Safe (liftWGPrefix action) :=
  entry_lift action (same.factor Packets.epoch) (same.factor stagedAt)

theorem entry_ambient (action : AmbientM α) :
    StatePrefixPreserves (Entry generation pid allocation Safe) Safe
      (liftWGPrefix (monadLift action : WG.M α)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.2)
  intro h w a value v b before run
  exact (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient action (fun w => Entry generation pid allocation Safe h w a))
    w a value v b before run

theorem entry_read_key (kid : KeypairId) :
    StatePrefixPreserves (Entry generation pid allocation Safe) Safe (liftWGPrefix (getKeypair kid)) :=
  entry_lift _ (PacketOrigins.epoch_ring (TxRing.getKeypair_frame kid)) (Exact.read_key kid)

theorem entry_write_key (kid : KeypairId) (key : Keypair) :
    StatePrefixPreserves (Entry generation pid allocation Safe) Safe (liftWGPrefix (setKeypair kid key)) :=
  entry_lift _ (key_write_epoch kid key) (set_key_staged kid key)

theorem entry_key_put (kid : Option KeypairId) :
    StatePrefixPreserves (Entry generation pid allocation Safe) Safe (liftWGPrefix (keypairPut kid false)) :=
  entry_lift _ (PacketOrigins.epoch_ring (TxRing.keypairPut_frame kid false)) (Exact.key_put kid false)

theorem entry_key_get (kid : Option KeypairId) :
    StatePrefixPreserves (Entry generation pid allocation Safe) Safe (liftWGPrefix (keypairGet kid)) :=
  entry_lift _ (PacketOrigins.epoch_ring ((RetirementSecurity.keyGet_cryptWire kid).factor Prod.fst))
    (key_get_staged kid)

theorem entry_reserve (kid : KeypairId) :
    StatePrefixPreserves (Entry generation pid allocation Safe) Safe (liftWGPrefix (Nonce.reserveNative kid)) :=
  entry_lift _ (reserve_epoch kid) (reserve_staged kid)

theorem entry_pure (value : α) :
    StatePrefixPreserves (Entry generation pid allocation Safe) Safe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ before => before.2) (fun _ _ _ before => before)

/-- The exact original prefix immediately preceding restore keeps the target
queue empty under the same allocation, even if the borrowed key is removed. -/
theorem prefix_entry (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StatePrefixPreserves (Entry generation pid allocation Safe) Safe
      (prefixWith liftWGPrefix packets keypair invalid) := by
  have tail (kp : Option KeypairId) :
      StatePrefixPreserves (Entry generation pid allocation Safe) Safe (do
        liftWGPrefix (keypairPut kp false)
        for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
        _ ← liftWGPrefix (branch .stagedOrphanWalk false)) := by
    apply StatePrefixEnsures.bind (entry_key_put kp)
    intro _
    apply StatePrefixEnsures.bind
    · apply StatePrefixEnsures.forInInvariant packets PUnit.unit _
        (fun _ => Entry generation pid allocation Safe) Safe
        (fun _ _ _ _ before => before.2)
      intro packet acc
      exact StatePrefixEnsures.bind (entry_ambient (AmbientM.branch .stagedOrphanWalk true))
        (fun _ => entry_pure _)
    · intro _
      exact StatePrefixEnsures.bind (entry_ambient (AmbientM.branch .stagedOrphanWalk false))
        (fun _ => entry_pure _)
  unfold prefixWith
  dsimp only
  split
  · split
    · apply StatePrefixEnsures.bind (entry_read_key _)
      intro key
      exact StatePrefixEnsures.bind (entry_write_key _ _) (fun _ => tail _)
    · exact StatePrefixEnsures.bind (entry_ambient (AmbientM.invariant "unreachable"))
        (fun _ => tail _)
  · exact tail _

/-- The source take itself supplies the empty queue and actual peer allocation;
there is no incoming vacancy assumption. -/
theorem take_vacant (r : Take.Receipt) (valid : r.Valid)
    (selected : r.run.value = some peer) :
    ∃ generation, Packets.epoch r.run.before = some generation ∧
      Vacant generation r.pid peer.internalId r.run.after := by
  obtain ⟨generation,epoch,same,_,empty,_⟩ := take_receipt_views r valid peer selected
  exact ⟨generation,epoch,same.trans epoch,empty⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreEntry
