import Leanux.Proofs.WG.Progress.FlushQueueModel
import Leanux.Proofs.WG.TimerDiscipline.WorkStateFrames
import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Config.LiveRemovalFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Noise TimerDiscipline Std.Do

def flushQueueKernel (k : Kernel) : Option WorkQueues := k.wg.map workQueues
def flushQueueAt (w : World) : Option WorkQueues := flushQueueKernel w.k

/-- Project the existing exact C2 table-removal effect. -/
theorem indexRemove_flushQueues (owner : IndexOwner) (queues : WorkQueues) :
    ⦃fun w => ⌜flushQueueAt w = some queues⌝⦄ indexRemove owner
      ⦃⇓? _ w => ⌜flushQueueAt w = some queues⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [flushQueueAt, flushQueueKernel, hd] at pre
  | some d =>
    obtain ⟨out, after, execution, device⟩ := Index.indexRemove_exact owner d w hd
    rw [run] at execution
    cases execution
    simpa [flushQueueAt, flushQueueKernel, workQueues, device, hd] using pre

/-- Variant of Keypairs/Frames/WGBase.peerPut_spec for both work queues,
which its shared snapshot does not contain. Last-reference deletion is included. -/
theorem peerPut_spec_queue_variant (peer : Option PeerId) (queues : WorkQueues) :
    ⦃fun w => ⌜flushQueueAt w = some queues⌝⦄ peerPut peer
      ⦃⇓? _ w => ⌜flushQueueAt w = some queues⌝⦄ := by
  have hi := fun owner => indexRemove_flushQueues owner queues
  mvcgen [peerPut, requireNotPending, refcountDecAndTest, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, branchCmp, invariant, unsupported,
    retirePeerUnits, hi]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [flushQueueAt, flushQueueKernel, workQueues, Option.map_map,
    Function.comp_def]
  all_goals grind

/-- Variant of Keypairs/Frames/WGTransitions.handshakeClear_spec for the two
queues absent from its snapshot; table removal uses the existing C2 effect. -/
theorem handshakeClear_spec_queue_variant (pid : PeerId) (queues : WorkQueues) :
    ⦃fun w => ⌜flushQueueAt w = some queues⌝⦄ handshakeClear pid
      ⦃⇓? _ w => ⌜flushQueueAt w = some queues⌝⦄ := by
  have hi := fun owner => indexRemove_flushQueues owner queues
  mvcgen [handshakeClear, IndexOwner.peerDeref, IndexOwner.peerWord, handshakeZero,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, unsupported, hi]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [flushQueueAt, flushQueueKernel, workQueues, Option.map_map,
    Function.comp_def]
  all_goals grind

/-- Queue preservation is projected from the existing exact C2 clearing relation;
no additional keypair-release or slot-update proof is needed. -/
theorem keypairsClear_flushQueues (pid : PeerId) (queues : WorkQueues) :
    ⦃fun w => ⌜flushQueueAt w = some queues⌝⦄ keypairsClear pid
      ⦃⇓? _ w => ⌜flushQueueAt w = some queues⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [flushQueueAt, flushQueueKernel, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      have failed : (getPeer pid).run w = .error (.invariant s!"dangling peer {pid}") := by
        simp [getPeer, getDev, getK, invariant, hd, hp]
        rfl
      change ((getPeer pid).run w >>= _) = .ok (result, final) at run
      rw [failed] at run
      cases run
    | some p =>
      obtain ⟨after, device, effect⟩ := keypairsClear_effect pid d p hp w result final hd run
      have same := congrArg (fun x => (x.1, x.2.1)) (Config.clearRun_cleanupContext effect)
      have equal : workQueues after = workQueues d := by
        simpa [workQueues, Config.cleanupContext] using same
      simpa [flushQueueAt, flushQueueKernel, device, hd, equal] using pre

theorem sendHandshakeInitiation_flushQueues (pid : PeerId) (queues : WorkQueues) :
    ⦃fun w => ⌜flushQueueAt w = some queues⌝⦄ sendHandshakeInitiation pid
      ⦃⇓? _ w => ⌜flushQueueAt w = some queues⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [flushQueueAt, flushQueueKernel, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      have failed : (getPeer pid).run w = .error (.invariant s!"dangling peer {pid}") := by
        simp [getPeer, getDev, getK, invariant, hd, hp]
        rfl
      change ((getPeer pid).run w >>= _) = .ok (result, final) at run
      rw [failed] at run
      cases run
    | some p =>
      have h := sendHandshakeInitiation_queueWorkView pid queues p.handshakePending
        w result final (by
          apply Prod.ext
          · exact pre
          · simp [queueWorkAt, queueWorkKernel, hd, hp]) run
      exact congrArg Prod.fst h

theorem handshakeSendWorker_flushQueues (pid : PeerId) (queues : WorkQueues) :
    ⦃fun w => ⌜flushQueueAt w = some queues⌝⦄ handshakeSendWorker pid
      ⦃⇓? _ w => ⌜flushQueueAt w = some queues⌝⦄ := by
  have hs := sendHandshakeInitiation_flushQueues pid queues
  have hp := peerPut_spec_queue_variant (some pid) queues
  mvcgen [handshakeSendWorker, hs, hp]

theorem queuedExpiredZeroKeyMaterial_flushQueues (pid : PeerId) (queues : WorkQueues) :
    ⦃fun w => ⌜flushQueueAt w = some queues⌝⦄ queuedExpiredZeroKeyMaterial pid
      ⦃⇓? _ w => ⌜flushQueueAt w = some queues⌝⦄ := by
  have hh := handshakeClear_spec_queue_variant pid queues
  have hk := keypairsClear_flushQueues pid queues
  have hp := peerPut_spec_queue_variant (some pid) queues
  mvcgen [queuedExpiredZeroKeyMaterial, hh, hk, hp]

end Leanux.Proofs.WG.Progress
