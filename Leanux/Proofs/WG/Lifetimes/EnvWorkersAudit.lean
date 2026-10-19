import Leanux.Proofs.WG.Lifetimes.BatchAudit
import Leanux.Proofs.WG.Lifetimes.PeerRemoval
import Leanux.Proofs.WG.Lifetimes.SavedPeerLookup
import Leanux.Proofs.Framing.EnvLeaves

/-! Actual deferred environment workers and their guards. Scheduler calls carry
reached speculative-entry markers; ordinary WG callees retain their focused
lifetime histories. Captured peer predicates are observed only when demanded. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def requireDrainedPrefix (what : String) (queues : List Bool) : PrefixM LifetimeEvent Unit := do
  if queues.any id then
    liftPrefix (unsupported s!"work {what} outlived the guest's wait (its records would be missing)")
  if let w :: _ ← liftPrefix pendingDeviceUnits then
    liftPrefix (unsupported s!"{w.symbol} is pending at the end of the wait (the dispatch its requeue causes has no section in the records)")
  let d ← liftWGObserver (liftWGPrefix getDev)
  if ← liftWGObserver (savedPeerAny (·.napiScheduled) d.peers.toList) then
    liftPrefix (invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)")

def requireIdleDevicePrefix : PrefixM LifetimeEvent Unit := do
  liftPrefix Env.requireNoCryptWork
  let d ← liftWGObserver (liftWGPrefix getDev)
  if !d.decryptQueue.empty then
    liftPrefix (unsupported "receive work queued at wg_stop (its worker's timing)")
  else if ← liftWGObserver (savedPeerAny (·.napiScheduled) d.peers.toList) then
    liftPrefix (unsupported "receive work queued at wg_stop (its worker's timing)")

theorem requireDrainedPrefix_erases (what : String) (queues : List Bool) :
    ErasesPrefix (requireDrainedPrefix what queues) (Env.requireDrained what queues) := by
  unfold requireDrainedPrefix Env.requireDrained
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | with_reducible apply erasesPrefix_bind_pure (by simpa only [liftWG_pure] using liftWGObserver_erases (savedPeerAny_erases _ _))
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)
  all_goals grind only

theorem requireIdleDevicePrefix_erases :
    ErasesPrefix requireIdleDevicePrefix Env.requireIdleDevice := by
  unfold requireIdleDevicePrefix Env.requireIdleDevice
  repeat' first
    | with_reducible apply erasesPrefix_bind_pure (by simpa only [liftWG_pure] using liftWGObserver_erases (savedPeerAny_erases _ _))
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Bool.false_or, Bool.true_or])
    | (with_reducible intro x; try dsimp only)

theorem requireDrainedPrefix_allocation (what : String) (queues : List Bool) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (requireDrainedPrefix what queues) := by
  let c := ProductAmbientContracts.ofNative allocationAmbient
  unfold requireDrainedPrefix
  have tail : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (do
      let d ← liftWGObserver (liftWGPrefix getDev)
      if ← liftWGObserver (savedPeerAny (·.napiScheduled) d.peers.toList) then
        liftPrefix (invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)")) := by
    apply ProductAmbientContracts.drop (Q := fun _ _ => True)
    apply PrefixEnsures.bind (getDev_saved_spec_product c (fun _ => True))
    intro d
    apply PrefixEnsures.bind (savedPeerAny_spec_product c (fun _ => True) _ _)
    intro pending
    split
    · exact c.invariant (fun _ => True) _
    · exact c.pure (fun _ => True) _
  have checked : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (do
      if let w :: _ ← liftPrefix pendingDeviceUnits then
        liftPrefix (unsupported s!"{w.symbol} is pending at the end of the wait (the dispatch its requeue causes has no section in the records)")
      let d ← liftWGObserver (liftWGPrefix getDev)
      if ← liftWGObserver (savedPeerAny (·.napiScheduled) d.peers.toList) then
        liftPrefix (invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)")) := by
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.ambient (fun _ => True) AmbientM.pendingDeviceUnits))
    intro workers
    cases workers with
    | nil => exact tail
    | cons worker rest =>
      exact PrefixPreserves.bind (ProductAmbientContracts.drop (c.ambient (fun _ => True) (AmbientM.unsupported _))) (fun _ => tail)
  split
  · exact PrefixPreserves.bind (ProductAmbientContracts.drop (c.ambient (fun _ => True) (AmbientM.unsupported _))) (fun _ => checked)
  · exact checked

theorem requireIdleDevicePrefix_allocation :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe requireIdleDevicePrefix := by
  let c := ProductAmbientContracts.ofNative allocationAmbient
  unfold requireIdleDevicePrefix
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.store (fun _ => True) _ requireNoCryptWork_sameKernel))
  intro _
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (getDev_saved_spec_product c (fun _ => True))
  intro d
  split
  · exact (c.unsupported (fun s => True ∧ SavedPeers d.peers.toList s) _).consequence
      (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, trivial⟩)
  · apply PrefixEnsures.bind (savedPeerAny_spec_product c (fun _ => True) _ _)
    intro pending
    split
    · exact c.unsupported (fun _ => True) _
    · exact c.pure (fun _ => True) _

def runCryptWorkersAudit : AuditM Unit := do
  scheduleAudit
  liftPrefix Env.deliverSent

def runOneSendWorkerAudit : AuditM Unit := do
  let d ← liftPrefix (liftWG getDev)
  let some headPid := d.sendWorkQueue.head? | liftPrefix (invariant "no queued handshake send work")
  let pid ← match ← liftPrefix (peekUnit .sendWorker) with
    | some u => liftPrefix (resolveUnit .sendWorker u d.sendWorkQueue)
    | none => pure headPid
  auditFocus (liftWGObserver (runFlushedSendWorkPrefix pid))

def runOneClearWorkerAudit : AuditM Unit := do
  let d ← liftPrefix (liftWG getDev)
  let some headPid := d.clearWorkQueue.head? | liftPrefix (invariant "no queued clear work")
  let pid ← match ← liftPrefix (peekUnit .clearPeerWorker) with
    | some u => liftPrefix (resolveUnit .clearPeerWorker u d.clearWorkQueue)
    | none => pure headPid
  auditFocus (liftWGObserver (runFlushedClearWorkPrefix pid))

def runSendWorkersAudit : AuditM Unit := do
  if (← liftPrefix getWG).dev.isNone then return
  liftPrefix Env.requireNoCryptWork
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then liftPrefix Env.deliverSent; return
    runOneSendWorkerAudit
    scheduleAudit
  liftPrefix (budgetExhausted "the send work queue")

def afterXmitAudit : AuditM Unit := do
  let some d := (← liftPrefix getWG).dev | return
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    liftPrefix (unsupported "wg_xmit queued crypt work and a handshake (their order)")
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if crypt then
    runCryptWorkersAudit
    let d ← liftPrefix (liftWG getDev)
    auditFocus (requireDrainedPrefix "wg_xmit queued" [!d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  runSendWorkersAudit

theorem runCryptWorkersAudit_erases : ErasesPrefix runCryptWorkersAudit Env.runCryptWorkers :=
  erasesPrefix_bind (scheduleAudit_erases _) (fun _ => erasesPrefix_lift _)

/-- The non-NET_RX send section uses the same ordered records as the native
flush, and the canonical adapter threads the returned WG and Ambient state. -/
private theorem runFlushedSendWork_lift (pid : PeerId) :
    (do
      modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}
      let p ← getPeer pid
      if !p.handshakePending then invariant "queued work without a pending flag"
      setPeer pid {p with handshakePending := (← getDev).sendWorkQueue.contains pid}
      Env.runWorker .sendWorker (WG.handshakeSendWorker pid) : Leanux.M Unit) =
        liftWG (runFlushedSendWork pid) := by
  have ambient {α : Type} (a : AmbientM α) :
      liftWG (monadLift a : WG.M α) = (monadLift a : Leanux.M α) :=
    liftWG_ambient a
  have hw : (Worker.sendWorker == Worker.netRx) = false := rfl
  simp only [runFlushedSendWork, Env.runWorker, hw, Bool.false_eq_true, ite_false,
    liftWG_bind, liftWG_pure, apply_ite]
  simp only [hidden, invariant, ambient]
  all_goals rfl

/-- The clear section has no NET_RX fixture update; every native action and
both section records remain in their original order. -/
private theorem runFlushedClearWork_lift (pid : PeerId) :
    (do
      modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}
      Env.runWorker .clearPeerWorker (WG.queuedExpiredZeroKeyMaterial pid) : Leanux.M Unit) =
        liftWG (runFlushedClearWork pid) := by
  have ambient {α : Type} (a : AmbientM α) :
      liftWG (monadLift a : WG.M α) = (monadLift a : Leanux.M α) :=
    liftWG_ambient a
  have hw : (Worker.clearPeerWorker == Worker.netRx) = false := rfl
  simp only [runFlushedClearWork, Env.runWorker, hw, Bool.false_eq_true, ite_false,
    liftWG_bind, liftWG_pure]
  simp only [hidden, ambient]
  all_goals rfl

theorem runOneSendWorkerAudit_erases : ErasesPrefix runOneSendWorkerAudit Env.runOneSendWorker := by
  unfold runOneSendWorkerAudit Env.runOneSendWorker
  repeat' first
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals
    rw [runFlushedSendWork_lift]
    exact auditFocus_erases (liftWGObserver_erases (runFlushedSendWorkPrefix_erases _))

theorem runOneClearWorkerAudit_erases : ErasesPrefix runOneClearWorkerAudit Env.runOneClearWorker := by
  unfold runOneClearWorkerAudit Env.runOneClearWorker
  repeat' first
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals
    rw [runFlushedClearWork_lift]
    exact auditFocus_erases (liftWGObserver_erases (runFlushedClearWorkPrefix_erases _))

theorem runSendWorkersAudit_erases : ErasesPrefix runSendWorkersAudit Env.runSendWorkers := by
  unfold runSendWorkersAudit Env.runSendWorkers
  repeat' first
    | with_reducible exact scheduleAudit_erases _
    | with_reducible exact runOneSendWorkerAudit_erases
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterXmitAudit_erases : ErasesPrefix afterXmitAudit Env.afterXmit := by
  unfold afterXmitAudit Env.afterXmit
  repeat' first
    | with_reducible exact auditFocus_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible exact runSendWorkersAudit_erases
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runCryptWorkersAudit_preserves : PrefixPreserves AuditInv AuditSafe runCryptWorkersAudit :=
  PrefixPreserves.bind (scheduleAudit_preserves _) (fun _ =>
    auditLift_store _ (deliverSent_sameKernel.of_factor
      (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl)))

theorem runOneSendWorkerAudit_preserves : PrefixPreserves AuditInv AuditSafe runOneSendWorkerAudit := by
  apply PrefixEnsures.preserves
  unfold runOneSendWorkerAudit
  repeat' first
    | (audit_contract_head liftWGObserver; exact auditFocus_preserves (runFlushedSendWorkPrefix_preserves allocationAmbient allocationPeerRemoval _).liftWGObserver)
    | (audit_contract_head liftWG; exact auditLift_store _
        (sameView_liftWG (fun w => wgStoreView w.wg)
          wgStoreView getDev getDev_sameWGStore (fun _ _ _ hi => hi)))
    | (audit_contract_head liftPrefix; exact auditLift_store _ (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    | (audit_contract_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

theorem runOneClearWorkerAudit_preserves : PrefixPreserves AuditInv AuditSafe runOneClearWorkerAudit := by
  apply PrefixEnsures.preserves
  unfold runOneClearWorkerAudit
  repeat' first
    | (audit_contract_head liftWGObserver; exact auditFocus_preserves (runFlushedClearWorkPrefix_preserves allocationAmbient allocationPeerRemoval _).liftWGObserver)
    | (audit_contract_head liftWG; exact auditLift_store _
        (sameView_liftWG (fun w => wgStoreView w.wg)
          wgStoreView getDev getDev_sameWGStore (fun _ _ _ hi => hi)))
    | (audit_contract_head liftPrefix; exact auditLift_store _ (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    | (audit_contract_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

theorem runSendWorkersAudit_preserves : PrefixPreserves AuditInv AuditSafe runSendWorkersAudit := by
  apply PrefixEnsures.preserves
  unfold runSendWorkersAudit
  repeat' first
    | (audit_contract_head scheduleAudit; exact scheduleAudit_preserves _)
    | (audit_contract_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_preserves)
    | (audit_contract_head Env.deliverSent; exact auditLift_store _
        (deliverSent_sameKernel.of_factor (fun s : ProductStore43 => s.2.2.2)
          (fun w => wgStoreView w.wg) (fun _ => rfl)))
    | (audit_contract_head Env.requireNoCryptWork; exact auditLift_store _
        (requireNoCryptWork_sameKernel.of_factor (fun s : ProductStore43 => s.2.2.2)
          (fun w => wgStoreView w.wg) (fun _ => rfl)))
    | (audit_contract_head liftWG; exact auditLift_store _
        (sameView_liftWG (fun w => wgStoreView w.wg)
          wgStoreView getDev getDev_sameWGStore (fun _ _ _ hi => hi)))
    | (audit_contract_head getWG; exact auditLift_store _ (by
        intro initial
        exact productGetWG_spec (fun store => store.2.2.2 = initial)))
    | (audit_contract_head modifyWG; exact auditLift_store _ (by
        intro initial
        exact productModifyWG_spec (fun store => store.2.2.2 = initial) _ (fun _ => rfl)))
    | (audit_contract_head liftPrefix; exact auditLift_store _ (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    | (audit_contract_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
    | (audit_contract_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
        (I := fun _ h w => AuditInv h w) (hs := fun _ _ _ hi => hi.safe))
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

theorem afterXmitAudit_preserves : PrefixPreserves AuditInv AuditSafe afterXmitAudit := by
  apply PrefixEnsures.preserves
  unfold afterXmitAudit
  repeat' first
    | (audit_contract_head runCryptWorkersAudit; exact runCryptWorkersAudit_preserves)
    | (audit_contract_head runSendWorkersAudit; exact runSendWorkersAudit_preserves)
    | (audit_contract_head requireDrainedPrefix; exact auditFocus_preserves (requireDrainedPrefix_allocation _ _))
    | (audit_contract_head liftWG; exact auditLift_store _
        (sameView_liftWG (fun w => wgStoreView w.wg)
          wgStoreView getDev getDev_sameWGStore (fun _ _ _ hi => hi)))
    | (audit_contract_head getWG; exact auditLift_store _ (by
        intro initial
        exact productGetWG_spec (fun store => store.2.2.2 = initial)))
    | (audit_contract_head modifyWG; exact auditLift_store _ (by
        intro initial
        exact productModifyWG_spec (fun store => store.2.2.2 = initial) _ (fun _ => rfl)))
    | (audit_contract_head liftPrefix; exact auditLift_store _ (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    | (audit_contract_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
