import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceCreate
import Leanux.Proofs.WG.Queues.HolderAdmission
import Leanux.Proofs.WG.Queues.TxStagedHead

/-! Staging-prefix frames preserve packet allocation geometry and existing
physical occurrences. Key/peer release uses the original surviving-queue
frame; it does not assert that a released peer remains resident. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do
open Queues.RxCredits

namespace StagingOccurrences

def geometry (w : WGWorld) := (Packets.snapshot w,fun id => Queues.TxDisposition.txPackets w id)
abbrev Ready (locals : List TxLocalBatch) (w : WGWorld) := Packets.Inv w ∧ TxInventory locals w

private theorem modify_geometry (initial) (f : Device → Device)
    (frontier : ∀ d, (f d).nextSkb = d.nextSkb)
    (tx : ∀ d, (f d).txSkbs = d.txSkbs) (rx : ∀ d, (f d).rxSkbs = d.rxSkbs) :
    Preserves (fun w => geometry w = initial) (modifyDev f) := by
  apply hoare_modify
  intro w before
  cases hd : w.dev <;>
    simpa only [geometry,Packets.snapshot,Packets.deviceStore,Queues.TxDisposition.txPackets,
      hd,Option.map_none,Option.map_some,Option.bind_none,Option.bind_some,frontier,tx,rx] using before

macro "staging_geometry_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (allocation_release_head getPeer; exact getPeer_preserves _ _)
  | (allocation_release_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b hi run
     simpa only [(KeyTimes.getKeypair_return _ w v k a b run).1] using hi)
  | (allocation_release_head getDev; unfold getDev)
  | (allocation_release_head setPeer; unfold setPeer)
  | (allocation_release_head setKeypair; unfold setKeypair)
  | (allocation_release_head modifyDev
     apply modify_geometry $initial
     all_goals intro d; rfl)
  | (allocation_release_head get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM
     apply hoare_liftIndex
     intro w d table hi hd
     simpa only [geometry,Packets.snapshot,Packets.deviceStore,Queues.TxDisposition.txPackets,
       hd,Option.bind_some] using hi)
  | (allocation_release_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => geometry w = $initial))
  | (allocation_release_head ForIn.forIn
     apply list_view_spec id (fun w => geometry w = $initial)
     intro x b
     change Preserves (fun w => geometry w = $initial) _)
  | (allocation_release_head modify; apply hoare_modify; intro w hi; exact hi)
  | allocation_release_step)

theorem key_get_geometry (kid : Option KeypairId) : SameView geometry (keypairGet kid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' staging_geometry_step initial

theorem key_put_geometry (kid : Option KeypairId) (now : Bool) :
    SameView geometry (keypairPut kid now) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' staging_geometry_step initial

theorem peer_get_geometry (pid : PeerId) : SameView geometry (peerGet pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,unsupported]
  repeat' staging_geometry_step initial

theorem peer_put_geometry (pid : Option PeerId) : SameView geometry (peerPut pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold peerPut refcountDecAndTest retirePeerUnits
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,
    invariant,unsupported,modifyAmbient]
  repeat' staging_geometry_step initial

theorem queued_geometry (pid : PeerId) (retry : Bool) :
    SameView geometry (sendQueuedHandshakeInitiation pid retry) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (allocation_release_head peerGet; exact (peer_get_geometry _).wp (· = initial))
    | (allocation_release_head peerPut; exact (peer_put_geometry _).wp (· = initial))
    | staging_geometry_step initial

theorem no_key_geometry (pid : PeerId) (packets : List WG.Packet)
    (key : Option KeypairId) (invalid : Bool) :
    SameView geometry (stagedOutNokey pid packets key invalid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head keypairPut; exact (key_put_geometry _ _).wp (· = initial))
    | (allocation_release_head sendQueuedHandshakeInitiation; exact (queued_geometry _ _).wp (· = initial))
    | staging_geometry_step initial

abbrev QueueFrame (initial w : WGWorld) :=
  ∀ pid batches, handoffTxView w pid = some batches → handoffTxView initial pid = some batches

theorem queued_frame (pid : PeerId) (retry : Bool) (initial : WGWorld) :
    Preserves (QueueFrame initial) (sendQueuedHandshakeInitiation pid retry) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run q batches found
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (sendQueued_ownership pid retry) w a result v b run
  have queues := congrFun (congrArg (fun view => view.2.2.1) same) q
  have eq := congrArg (Option.map (fun fields : PeerOwnership => fields.2.1)) queues
  have sameQueue : handoffTxView v q = handoffTxView w q := by
    simpa only [ownershipPointView,ownershipAt,peerAt,handoffTxView,Option.map_map,
      Function.comp_def,peerOwnership] using eq
  exact before q batches (sameQueue.symm.trans found)

theorem key_frame {action : WG.M α}
    (frame : ∀ initial, Preserves (DurableHolders.Frame initial) action) (initial : WGWorld) :
    Preserves (QueueFrame initial) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run pid batches found
  have step := (hoare_iff_run_ambient _ _ _).mp (frame w) w a result v b
    (DurableHolders.Frame.refl w) run
  exact before pid batches (step.tx pid batches found)

theorem no_key_frame (pid : PeerId) (packets : List WG.Packet)
    (key : Option KeypairId) (invalid : Bool) (initial : WGWorld) :
    Preserves (QueueFrame initial) (stagedOutNokey pid packets key invalid) := by
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keypairPut; exact key_frame (HolderWorkFrames.keypairPut_frame _ _) initial)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued_frame _ _ initial)
    | (rx_retention_head getKeypair
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a k v b hi run
       simpa only [(KeyTimes.getKeypair_return _ w v k a b run).1] using hi)
    | (rx_retention_head setKeypair; unfold setKeypair)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (QueueFrame initial)
       intro x b
       change Preserves (QueueFrame initial) _)
    | tx_retained_step initial

theorem frame_ready {action : WG.M α} (shape : SameView geometry action)
    (queues : ∀ initial, Preserves (QueueFrame initial) action) :
    Preserves (Ready locals) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp shape w a result v b run
  have bounded : Packets.Inv v := by
    unfold Packets.Inv
    rw [show Packets.snapshot v = Packets.snapshot w from congrArg Prod.fst same]
    exact before.1
  refine ⟨bounded,before.2.transport ?_ ?_⟩
  · intro pid p found
    have step := (hoare_iff_run_ambient _ _ _).mp (queues w) w a result v b
      (fun _ _ h => h) run
    have old := step pid p.txQueue.all (by
      simpa [handoffTxView,peerAt] using congrArg (Option.map (fun p => p.txQueue.all)) found)
    change (peerAt w pid).map (fun p => p.txQueue.all) = some p.txQueue.all at old
    obtain ⟨q,resident,queue⟩ := Option.map_eq_some_iff.mp old
    exact ⟨q,resident,congrArg List.flatten queue⟩
  · intro id packet found
    exact ⟨packet,(congrFun (congrArg Prod.snd same) id).trans found⟩

theorem no_key_ready (pid : PeerId) (packets : List WG.Packet)
    (key : Option KeypairId) (invalid : Bool) :
    Preserves (Ready locals) (stagedOutNokey pid packets key invalid) :=
  frame_ready (no_key_geometry _ _ _ _) (no_key_frame _ _ _ _)

theorem key_get_ready (kid : Option KeypairId) : Preserves (Ready locals) (keypairGet kid) := by
  apply frame_ready (key_get_geometry kid)
  apply key_frame
  intro initial
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' holder_prepare_step initial

end StagingOccurrences
end Leanux.Proofs.WG.RetirementSecurity
