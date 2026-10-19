import Leanux.Proofs.WG.Queues.RxScheduleHistory
import Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit

/-! Deferred environment callers use the concrete stamped scheduler. Focused
send/drain leaves are poll-free in the source; their original access observations
and failure prefixes remain part of the same incoming audit history. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def runCryptWorkers : Obs Unit := do
  schedule
  liftPrefix Env.deliverSent

def runSendWorkers : Obs Unit := do
  if (← liftPrefix getWG).dev.isNone then return
  liftPrefix Env.requireNoCryptWork
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then liftPrefix Env.deliverSent; return
    audit runOneSendWorkerAudit
    schedule
  liftPrefix (budgetExhausted "the send work queue")

def afterXmit : Obs Unit := do
  let some d := (← liftPrefix getWG).dev | return
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    liftPrefix (unsupported "wg_xmit queued crypt work and a handshake (their order)")
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if crypt then
    runCryptWorkers
    let d ← liftPrefix (liftWG getDev)
    mixed (requireDrainedPrefix "wg_xmit queued" [!d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  runSendWorkers

theorem runCryptWorkers_erases : ErasesPrefix runCryptWorkers Env.runCryptWorkers := by
  unfold runCryptWorkers Env.runCryptWorkers
  exact erasesPrefix_bind (schedule_erases _) (fun _ => erasesPrefix_lift _)

theorem runCryptWorkers_preserves : PrefixPreserves BoundaryInv BoundarySafe runCryptWorkers := by
  unfold runCryptWorkers
  exact PrefixPreserves.bind (schedule_preserves _) (fun _ =>
    boundaryLift_kernel _ deliverSent_sameKernel)

theorem runCryptWorkers_projects : ProjectsUnder AuditInv auditEvent runCryptWorkers runCryptWorkersAudit := by
  unfold runCryptWorkers runCryptWorkersAudit
  exact projectsUnder_bind (schedule_projects _) (scheduleAudit_preserves _)
    (fun _ => projectsUnder_lift _ _)

theorem runSendWorkers_erases : ErasesPrefix runSendWorkers Env.runSendWorkers := by
  unfold runSendWorkers Env.runSendWorkers
  repeat' first
    | with_reducible exact runCryptWorkers_erases
    | with_reducible exact schedule_erases _
    | with_reducible exact audit_erases runOneSendWorkerAudit_erases
    | with_reducible exact mixed_erases (requireDrainedPrefix_erases _ _)
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runSendWorkers_preserves : PrefixPreserves BoundaryInv BoundarySafe runSendWorkers := by
  apply PrefixEnsures.preserves
  unfold runSendWorkers
  repeat' first
    | (audit_contract_head runCryptWorkers; exact runCryptWorkers_preserves)
    | (audit_contract_head runSendWorkers; exact runSendWorkers_preserves)
    | (audit_contract_head schedule; exact schedule_preserves _)
    | (audit_contract_head audit; exact audit_preserves _ runOneSendWorkerAudit_preserves)
    | (audit_contract_head mixed; exact mixed_preserves (requireDrainedPrefix_allocation _ _))
    | (audit_contract_head Env.deliverSent; exact boundaryLift_kernel _ deliverSent_sameKernel)
    | (audit_contract_head Env.requireNoCryptWork; exact boundaryLift_kernel _ requireNoCryptWork_sameKernel)
    | (audit_contract_head liftWG; exact boundaryLift_kernel _
        (liftWG_sameProductStore getDev getDev_sameWGStore))
    | (audit_contract_head getWG; exact boundaryLift_kernel _ (by
        intro initial
        exact productGetWG_spec (fun store => store = initial)))
    | (audit_contract_head modifyWG; exact boundaryLift_kernel _ (by
        intro initial
        exact productModifyWG_spec (fun store => store = initial) _ (fun _ => rfl)))
    | (audit_contract_head liftPrefix; exact boundaryLift_kernel _ (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    | (audit_contract_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
    | (audit_contract_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
        (I := fun _ h w => BoundaryInv h w) (hs := fun _ _ _ hi => hi.safe))
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => BoundaryInv h w))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

theorem runSendWorkers_projects : ProjectsUnder AuditInv auditEvent runSendWorkers runSendWorkersAudit := by
  unfold runSendWorkers runSendWorkersAudit
  repeat' first
    | (audit_contract ProjectsUnder; first
        | (audit_contract_head runCryptWorkers; exact runCryptWorkers_projects)
        | (audit_contract_head runSendWorkers; exact runSendWorkers_projects)
        | (audit_contract_head schedule; exact schedule_projects _)
        | (audit_contract_head audit; exact audit_projects runOneSendWorkerAudit_preserves)
        | (audit_contract_head mixed; exact mixed_projects (requireDrainedPrefix_allocation _ _))
        | (audit_contract_head liftPrefix; exact projectsUnder_lift _ _)
        | (audit_contract_head Pure.pure; exact projectsUnder_pure _ _)
        | (audit_contract_head ForIn.forIn; apply projectsUnder_range)
        | (audit_contract_head Bind.bind; apply projectsUnder_bind))
    | (audit_contract PrefixPreserves; first
        | (audit_contract_head runCryptWorkersAudit; exact runCryptWorkersAudit_preserves)
        | (audit_contract_head runSendWorkersAudit; exact runSendWorkersAudit_preserves)
        | (audit_contract_head scheduleAudit; exact scheduleAudit_preserves _)
        | (audit_contract_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_preserves)
        | (audit_contract_head requireDrainedPrefix; exact auditFocus_preserves (requireDrainedPrefix_allocation _ _))
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
        | (audit_contract_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _)
        | (audit_contract_head ForIn.forIn; apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe))
        | (audit_contract_head Bind.bind; apply PrefixPreserves.bind))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

theorem afterXmit_erases : ErasesPrefix afterXmit Env.afterXmit := by
  unfold afterXmit Env.afterXmit
  repeat' first
    | with_reducible exact runCryptWorkers_erases
    | with_reducible exact runSendWorkers_erases
    | with_reducible exact schedule_erases _
    | with_reducible exact audit_erases runOneSendWorkerAudit_erases
    | with_reducible exact mixed_erases (requireDrainedPrefix_erases _ _)
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterXmit_preserves : PrefixPreserves BoundaryInv BoundarySafe afterXmit := by
  apply PrefixEnsures.preserves
  unfold afterXmit
  repeat' first
    | (audit_contract_head runCryptWorkers; exact runCryptWorkers_preserves)
    | (audit_contract_head runSendWorkers; exact runSendWorkers_preserves)
    | (audit_contract_head schedule; exact schedule_preserves _)
    | (audit_contract_head audit; exact audit_preserves _ runOneSendWorkerAudit_preserves)
    | (audit_contract_head mixed; exact mixed_preserves (requireDrainedPrefix_allocation _ _))
    | (audit_contract_head Env.deliverSent; exact boundaryLift_kernel _ deliverSent_sameKernel)
    | (audit_contract_head Env.requireNoCryptWork; exact boundaryLift_kernel _ requireNoCryptWork_sameKernel)
    | (audit_contract_head liftWG; exact boundaryLift_kernel _
        (liftWG_sameProductStore getDev getDev_sameWGStore))
    | (audit_contract_head getWG; exact boundaryLift_kernel _ (by
        intro initial
        exact productGetWG_spec (fun store => store = initial)))
    | (audit_contract_head modifyWG; exact boundaryLift_kernel _ (by
        intro initial
        exact productModifyWG_spec (fun store => store = initial) _ (fun _ => rfl)))
    | (audit_contract_head liftPrefix; exact boundaryLift_kernel _ (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    | (audit_contract_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
    | (audit_contract_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
        (I := fun _ h w => BoundaryInv h w) (hs := fun _ _ _ hi => hi.safe))
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => BoundaryInv h w))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

theorem afterXmit_projects : ProjectsUnder AuditInv auditEvent afterXmit afterXmitAudit := by
  unfold afterXmit afterXmitAudit
  repeat' first
    | (audit_contract ProjectsUnder; first
        | (audit_contract_head runCryptWorkers; exact runCryptWorkers_projects)
        | (audit_contract_head runSendWorkers; exact runSendWorkers_projects)
        | (audit_contract_head schedule; exact schedule_projects _)
        | (audit_contract_head audit; exact audit_projects runOneSendWorkerAudit_preserves)
        | (audit_contract_head mixed; exact mixed_projects (requireDrainedPrefix_allocation _ _))
        | (audit_contract_head liftPrefix; exact projectsUnder_lift _ _)
        | (audit_contract_head Pure.pure; exact projectsUnder_pure _ _)
        | (audit_contract_head ForIn.forIn; apply projectsUnder_range)
        | (audit_contract_head Bind.bind; apply projectsUnder_bind))
    | (audit_contract PrefixPreserves; first
        | (audit_contract_head runCryptWorkersAudit; exact runCryptWorkersAudit_preserves)
        | (audit_contract_head runSendWorkersAudit; exact runSendWorkersAudit_preserves)
        | (audit_contract_head scheduleAudit; exact scheduleAudit_preserves _)
        | (audit_contract_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_preserves)
        | (audit_contract_head requireDrainedPrefix; exact auditFocus_preserves (requireDrainedPrefix_allocation _ _))
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
        | (audit_contract_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _)
        | (audit_contract_head ForIn.forIn; apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe))
        | (audit_contract_head Bind.bind; apply PrefixPreserves.bind))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

/-- Direct projection of the original section wrapper, including its failure
before NET_RX cleanup. The body receives the actual produced history. -/
theorem runWorker_projects (worker : Worker) {g : Obs Unit} {a : AuditM Unit}
    (hg : ProjectsUnder AuditInv auditEvent g a)
    (ha : PrefixPreserves AuditInv AuditSafe a) :
    ProjectsUnder AuditInv auditEvent (runWorkerPrefix worker g) (runWorkerPrefix worker a) := by
  unfold runWorkerPrefix
  repeat' first
    | exact hg
    | exact ha
    | exact projectsUnder_lift _ _
    | exact projectsUnder_pure _ _
    | exact auditLift_store _ (by
        intro initial
        exact productAmbient_spec (AmbientM.hidden _) _ (fun _ _ hi => hi))
    | exact auditLift_store _ (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | apply projectsUnder_bind
    | apply PrefixPreserves.bind
    | split
    | (intro x; try dsimp only)

end Leanux.Proofs.WG.Queues.RxHistory
