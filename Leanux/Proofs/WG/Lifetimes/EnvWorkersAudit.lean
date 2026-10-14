import Leanux.Proofs.WG.Lifetimes.BatchAudit
import Leanux.Proofs.WG.Lifetimes.PeerRemoval
import Leanux.Proofs.WG.Lifetimes.SavedPeerLookup
import Leanux.Proofs.Framing.EnvLeaves

/-! Actual deferred environment workers and their guards. Scheduler calls carry
reached speculative-entry markers; ordinary WG callees retain their focused
lifetime histories. Captured peer predicates are observed only when demanded. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def requireDrainedPrefix (what : String) (queues : List Bool) : MixedM Unit := do
  if queues.any id then
    liftPrefix (unsupported s!"work {what} outlived the guest's wait (its records would be missing)")
  let d ← liftPrefix getDev
  if ← savedPeerAny (·.napiScheduled) d.peers.toList then
    liftPrefix (invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)")

def requireIdleDevicePrefix : MixedM Unit := do
  liftPrefix Env.requireNoCryptWork
  let d ← liftPrefix getDev
  if !d.decryptQueue.empty then
    liftPrefix (unsupported "receive work queued at wg_stop (its worker's timing)")
  else if ← savedPeerAny (·.napiScheduled) d.peers.toList then
    liftPrefix (unsupported "receive work queued at wg_stop (its worker's timing)")

theorem requireDrainedPrefix_erases (what : String) (queues : List Bool) :
    ErasesPrefix (requireDrainedPrefix what queues) (Env.requireDrained what queues) := by
  unfold requireDrainedPrefix Env.requireDrained
  repeat' first
    | with_reducible apply erasesPrefix_bind_pure (savedPeerAny_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem requireIdleDevicePrefix_erases :
    ErasesPrefix requireIdleDevicePrefix Env.requireIdleDevice := by
  unfold requireIdleDevicePrefix Env.requireIdleDevice
  repeat' first
    | with_reducible apply erasesPrefix_bind_pure (savedPeerAny_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Bool.or_true, Bool.false_or, Bool.true_or, Bool.true_eq, Bool.false_eq_true, not_false_eq_true, reduceIte])
    | (with_reducible intro x; try dsimp only)

theorem requireDrainedPrefix_allocation (what : String) (queues : List Bool) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (requireDrainedPrefix what queues) := by
  unfold requireDrainedPrefix
  have tail : PrefixPreserves AllocationInv LifetimeEvent.Safe (do
      let d ← liftPrefix getDev
      if ← savedPeerAny (·.napiScheduled) d.peers.toList then
        liftPrefix (invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)")) := by
    apply AmbientContracts.drop (Q := fun _ _ => True)
    apply PrefixEnsures.bind (getDev_saved_spec allocationAmbient (fun _ => True))
    intro d
    apply PrefixEnsures.bind (savedPeerAny_spec allocationAmbient (fun _ => True) _ _)
    intro pending
    split
    · exact allocationAmbient.invariant (fun _ => True) _
    · exact allocationAmbient.pure (fun _ => True) _
  split
  · exact PrefixPreserves.bind (allocation_kernel _ (by intro w x v hr; cases hr)) (fun _ => tail)
  · exact tail

theorem requireIdleDevicePrefix_allocation :
    PrefixPreserves AllocationInv LifetimeEvent.Safe requireIdleDevicePrefix := by
  unfold requireIdleDevicePrefix
  apply PrefixPreserves.bind (allocation_kernel _ requireNoCryptWork_sameKernel)
  intro _
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (getDev_saved_spec allocationAmbient (fun _ => True))
  intro d
  split
  · exact (allocationAmbient.unsupported (fun s => True ∧ SavedPeers d.peers.toList s) _).consequence
      (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, trivial⟩)
  · apply PrefixEnsures.bind (savedPeerAny_spec allocationAmbient (fun _ => True) _ _)
    intro pending
    split
    · exact allocationAmbient.unsupported (fun _ => True) _
    · exact allocationAmbient.pure (fun _ => True) _

def runCryptWorkersAudit : AuditM Unit := do
  scheduleAudit
  liftPrefix Env.deliverSent

def runOneSendWorkerAudit : AuditM Unit := do
  let d ← liftPrefix getDev
  let some headPid := d.sendWorkQueue.head? | liftPrefix (invariant "no queued handshake send work")
  let pid ← match ← liftPrefix (peekUnit .sendWorker) with
    | some u => liftPrefix (resolveUnit .sendWorker u d.sendWorkQueue)
    | none => pure headPid
  auditFocus (runFlushedSendWorkPrefix pid)

def runOneClearWorkerAudit : AuditM Unit := do
  let d ← liftPrefix getDev
  let some headPid := d.clearWorkQueue.head? | liftPrefix (invariant "no queued clear work")
  let pid ← match ← liftPrefix (peekUnit .clearPeerWorker) with
    | some u => liftPrefix (resolveUnit .clearPeerWorker u d.clearWorkQueue)
    | none => pure headPid
  auditFocus (runFlushedClearWorkPrefix pid)

def runSendWorkersAudit : AuditM Unit := do
  if (← liftPrefix getK).wg.isNone then return
  liftPrefix Env.requireNoCryptWork
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix getDev).sendWorkQueue.isEmpty then liftPrefix Env.deliverSent; return
    runOneSendWorkerAudit
    scheduleAudit
  liftPrefix (budgetExhausted "the send work queue")

def afterXmitAudit : AuditM Unit := do
  let some d := (← liftPrefix getK).wg | return
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    liftPrefix (unsupported "wg_xmit queued crypt work and a handshake (their order)")
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  if crypt then
    runCryptWorkersAudit
    let d ← liftPrefix getDev
    auditFocus (requireDrainedPrefix "wg_xmit queued" [!d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  runSendWorkersAudit

theorem runCryptWorkersAudit_erases : ErasesPrefix runCryptWorkersAudit Env.runCryptWorkers := by
  unfold runCryptWorkersAudit Env.runCryptWorkers
  repeat' first
    | with_reducible exact scheduleAudit_erases _
    | with_reducible exact auditFocus_erases (runFlushedSendWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (runFlushedClearWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runOneSendWorkerAudit_erases : ErasesPrefix runOneSendWorkerAudit Env.runOneSendWorker := by
  unfold runOneSendWorkerAudit Env.runOneSendWorker
  repeat' first
    | with_reducible exact scheduleAudit_erases _
    | with_reducible exact auditFocus_erases (runFlushedSendWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (runFlushedClearWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runOneClearWorkerAudit_erases : ErasesPrefix runOneClearWorkerAudit Env.runOneClearWorker := by
  unfold runOneClearWorkerAudit Env.runOneClearWorker
  repeat' first
    | with_reducible exact scheduleAudit_erases _
    | with_reducible exact auditFocus_erases (runFlushedSendWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (runFlushedClearWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runSendWorkersAudit_erases : ErasesPrefix runSendWorkersAudit Env.runSendWorkers := by
  unfold runSendWorkersAudit Env.runSendWorkers
  repeat' first
    | with_reducible exact scheduleAudit_erases _
    | with_reducible exact auditFocus_erases (runFlushedSendWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (runFlushedClearWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact runOneClearWorkerAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterXmitAudit_erases : ErasesPrefix afterXmitAudit Env.afterXmit := by
  unfold afterXmitAudit Env.afterXmit
  repeat' first
    | with_reducible exact scheduleAudit_erases _
    | with_reducible exact auditFocus_erases (runFlushedSendWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (runFlushedClearWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact runOneClearWorkerAudit_erases
    | with_reducible exact runSendWorkersAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runCryptWorkersAudit_preserves : PrefixPreserves AuditInv AuditSafe runCryptWorkersAudit := by
  unfold runCryptWorkersAudit
  repeat' first
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact auditFocus_preserves (runFlushedSendWorkPrefix_preserves allocationAmbient allocationPeerRemoval _)
    | with_reducible exact auditFocus_preserves (runFlushedClearWorkPrefix_preserves allocationAmbient allocationPeerRemoval _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ (resolveUnit_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (budgetExhausted_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runOneSendWorkerAudit_preserves : PrefixPreserves AuditInv AuditSafe runOneSendWorkerAudit := by
  unfold runOneSendWorkerAudit
  repeat' first
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact auditFocus_preserves (runFlushedSendWorkPrefix_preserves allocationAmbient allocationPeerRemoval _)
    | with_reducible exact auditFocus_preserves (runFlushedClearWorkPrefix_preserves allocationAmbient allocationPeerRemoval _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ (resolveUnit_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (budgetExhausted_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runOneClearWorkerAudit_preserves : PrefixPreserves AuditInv AuditSafe runOneClearWorkerAudit := by
  unfold runOneClearWorkerAudit
  repeat' first
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact auditFocus_preserves (runFlushedSendWorkPrefix_preserves allocationAmbient allocationPeerRemoval _)
    | with_reducible exact auditFocus_preserves (runFlushedClearWorkPrefix_preserves allocationAmbient allocationPeerRemoval _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ (resolveUnit_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (budgetExhausted_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runSendWorkersAudit_preserves : PrefixPreserves AuditInv AuditSafe runSendWorkersAudit := by
  unfold runSendWorkersAudit
  repeat' first
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact auditFocus_preserves (runFlushedSendWorkPrefix_preserves allocationAmbient allocationPeerRemoval _)
    | with_reducible exact auditFocus_preserves (runFlushedClearWorkPrefix_preserves allocationAmbient allocationPeerRemoval _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact runOneClearWorkerAudit_preserves
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ (resolveUnit_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (budgetExhausted_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterXmitAudit_preserves : PrefixPreserves AuditInv AuditSafe afterXmitAudit := by
  unfold afterXmitAudit
  repeat' first
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact auditFocus_preserves (runFlushedSendWorkPrefix_preserves allocationAmbient allocationPeerRemoval _)
    | with_reducible exact auditFocus_preserves (runFlushedClearWorkPrefix_preserves allocationAmbient allocationPeerRemoval _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact runOneClearWorkerAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ (resolveUnit_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (budgetExhausted_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
