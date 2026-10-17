import Leanux.Proofs.WG.Progress.FlushQueueModel
import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Config.LiveRemovalFrames
import Leanux.Proofs.WG.Index.PeerReleaseTableFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Noise TimerDiscipline Std.Do

def flushQueueKernel (g : WGWorld) : Option WorkQueues := g.dev.map workQueues
def flushQueueAt (g : WGWorld) : Option WorkQueues := flushQueueKernel g

/-- Both queues are retained on every normal release, including last-reference deletion. -/
theorem peerPut_spec_queue_variant (peer : Option PeerId) (queues : WorkQueues) :
    ⦃fun g => ⌜flushQueueAt g = some queues⌝⦄ peerPut peer
      ⦃⇓? _ g => ⌜flushQueueAt g = some queues⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases peer with
  | none =>
    simp [peerPut, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact pre
  | some pid =>
    cases device : g.dev with
    | none => simp [flushQueueAt, flushQueueKernel, device] at pre
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [peerPut, branch, AmbientM.branch, requireNotPending, getPeer, getDev,
          device, resident, invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0
        · simp [peerPut, branch, AmbientM.branch, requireNotPending, getPeer, getDev,
            device, resident, zero, refcountDecAndTest, branchCmp, AmbientM.branchCmp,
            invariant, AmbientM.invariant] at run
          cases run
        · have effect := Index.peerPut_exact pid d p resident (by omega) g ambient device
          change (match Index.peerReleaseRefusal pid p with
            | some stop => Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .error stop
            | none => ∃ s, Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) =
              .ok ((), s) ∧ s.wg.device = some (Index.releasedPeerDevice d pid p)) at effect
          rw [run] at effect
          cases refused : Index.peerReleaseRefusal pid p with
          | some stop => simp [refused, Campaign2.observeResult, Except.map] at effect
          | none =>
            simp only [refused, Campaign2.observeResult, Except.map] at effect
            obtain ⟨s, equality, actual⟩ := effect
            cases equality
            change final.dev = some (Index.releasedPeerDevice d pid p) at actual
            by_cases last : p.refcount = 1 <;>
              simpa [flushQueueAt, flushQueueKernel, device, actual, workQueues,
                Index.releasedPeerDevice, last] using pre

/-- Queue preservation remains substantive for the native handshake clear. -/
theorem handshakeClear_spec_queue_variant (pid : PeerId) (queues : WorkQueues) :
    ⦃fun g => ⌜flushQueueAt g = some queues⌝⦄ handshakeClear pid
      ⦃⇓? _ g => ⌜flushQueueAt g = some queues⌝⦄ := by
  let P : WGWorld → Prop := fun g => flushQueueAt g = some queues
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient result final after pre run).1
  have hderef : Ensures (IndexOwner.peerDeref (.handshake pid)) P (fun _ => P) := by
    unfold IndexOwner.peerDeref IndexOwner.peerWord
    refine ensures_bind _ _ (ensures_bind _ _ hread (fun p => hpure p.handshakeEntryPeer)) ?_
    intro word
    cases word with
    | none =>
      exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
        (AmbientM.unsupported "entry->peer is NULL: the C dereferences it") P)
    | some target => exact hpure target
  have hremove : Ensures (liftIndex (indexRemove (.handshake pid))) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftIndex_variant _ P (by
      intro g d table pre device
      simpa [P, flushQueueAt, flushQueueKernel, workQueues, device] using pre))
  apply (ensures_iff _ _ _).mp
  unfold handshakeClear
  refine ensures_bind _ _ hderef ?_
  intro _
  refine ensures_bind _ _ hremove ?_
  intro _
  unfold handshakeZero
  refine ensures_bind _ _ hread ?_
  intro p g ambient result final after pre run
  simp [setPeer, modifyDev] at run
  rcases run with ⟨rfl, rfl⟩
  simpa [P, flushQueueAt, flushQueueKernel, workQueues, Option.map_map, Function.comp_def] using pre

theorem keypairsClear_flushQueues (pid : PeerId) (queues : WorkQueues) :
    ⦃fun g => ⌜flushQueueAt g = some queues⌝⦄ keypairsClear pid
      ⦃⇓? _ g => ⌜flushQueueAt g = some queues⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases device : g.dev with
  | none => simp [flushQueueAt, flushQueueKernel, device] at pre
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      have failed : ((getPeer pid).run g).run ambient = .error (.invariant s!"dangling peer {pid}") := by
        simp [getPeer, getDev, invariant, AmbientM.invariant, device, resident]
        rfl
      change (((getPeer pid).run g).run ambient >>= _) = _ at run
      rw [failed] at run
      cases run
    | some p =>
      obtain ⟨out, present, effect⟩ := keypairsClear_effect pid d p resident g ambient result final after device run
      have same := congrArg (fun x => (x.1, x.2.1)) (Config.clearRun_cleanupContext effect)
      have equal : workQueues out = workQueues d := by
        simpa [workQueues, Config.cleanupContext] using same
      simpa [flushQueueAt, flushQueueKernel, present, device, equal] using pre

theorem queuedExpiredZeroKeyMaterial_flushQueues (pid : PeerId) (queues : WorkQueues) :
    ⦃fun g => ⌜flushQueueAt g = some queues⌝⦄ queuedExpiredZeroKeyMaterial pid
      ⦃⇓? _ g => ⌜flushQueueAt g = some queues⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold queuedExpiredZeroKeyMaterial
  exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (handshakeClear_spec_queue_variant pid queues))
    (fun _ => ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairsClear_flushQueues pid queues))
      (fun _ => (ensures_iff _ _ _).mpr (peerPut_spec_queue_variant (some pid) queues)))

end Leanux.Proofs.WG.Progress
