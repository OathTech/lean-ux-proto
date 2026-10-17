import Leanux.Proofs.WG.Queues.HolderAfterBatch
import Leanux.Proofs.WG.Queues.InjectAccount

/-! Completion of the recorded batch wait is derived from its actual final
queue guard. Placeholder execution takes a different source branch and is
not covered by this endpoint theorem. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AfterBatchCompletion
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

def wait : RxHistory.Obs Unit := do
  for _ in [0:(← liftPrefix recordBudget)] do
    RxHistory.schedule none
    if (← liftPrefix Env.peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id &&
        !(← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then
      RxHistory.audit runOneSendWorkerAudit
    else break

def finish : RxHistory.Obs Unit := do
  let d ← liftPrefix (liftWG getDev)
  RxHistory.mixed (requireDrainedPrefix "the batch queued"
    [!d.decryptQueue.empty,!d.encryptQueue.empty,!d.txWorkQueue.isEmpty,!d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty,d.handshakeQueueLen != 0])
  liftPrefix Env.deliverSent

theorem source_factor : RxHistory.afterBatch = (do
    liftPrefix (modifyWG fun w => {w with queuedThisCall:=[]})
    if (← liftPrefix getAmbient).hidden.isNone then
      RxHistory.runCryptWorkers
      RxHistory.runSendWorkers
    else
      wait
      finish) := by
  rw [TrafficSource.afterBatch_factor]
  simp only [TrafficSource.afterBatchWith,wait,finish,bind_assoc,bind_pure_unit]

theorem wait_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe wait := by
  have safe : ∀ h w,HolderAuxiliary.Inv initial loans before h w → OwnerChecks.Safe h :=
    fun _ _ hi => hi.2.1.safe
  have saved : ∀ h w v,productStoreView v=productStoreView w →
      HolderAuxiliary.Inv initial loans before h w → HolderAuxiliary.Inv initial loans before h v :=
    fun _ _ _ same hi => HolderAuxiliary.store hi same
  unfold wait
  repeat' first
    | (scheduler_preserve_at RxHistory.schedule; exact HandshakeWorker.schedule _ _ _ _)
    | (scheduler_preserve_at runOneSendWorkerAudit; exact HolderAuxSend.sendOne _ _ _)
    | deferred_raw_steps safe saved

/-- The source's final flags contain the actual decrypt-ring test. The next
operation is deliverSent, whose store frame retains the derived empty account. -/
theorem finish_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : runPrefix finish w h=(.ok ((),v),k)) :
    ∃ suffix, h=before++suffix ∧ remaining initial (NapiCarrier.removedPackets suffix)=[] ∧
      HolderAuxiliary.Inv [] loans k k v ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket), v.wg.dev=some d → d.rxSkbs[id]?≠some packet) := by
  unfold finish at run
  have read : (liftWG getDev).run w = match w.wg.dev with
      | none => .error (.invariant "no WireGuard device in this trace's fixture")
      | some d => .ok (d,w) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.RxDrainBoundary.«0».Leanux.Proofs.WG.Queues.RxCredits.readDev) w
  rw [runPrefix_bind,runPrefix_lift,read] at run
  cases hd:w.wg.dev with
  | none => simp only [hd] at run; cases run
  | some d =>
    simp only [hd] at run
    obtain ⟨x,u,j,drain,tail⟩ := DecryptIteration.bind_normal run
    cases x
    have flag : ∀ d',w.wg.dev=some d' → (!d'.decryptQueue.empty)∈
        [!d.decryptQueue.empty,!d.encryptQueue.empty,!d.txWorkQueue.isEmpty,!d.sendWorkQueue.isEmpty,
         !d.handshakeQueue.empty,d.handshakeQueueLen != 0] := by
      intro d' other
      have eq := hd.symm.trans other
      cases eq
      exact List.mem_cons_self ..
    obtain ⟨suffix,hist,empty,noPackets,post⟩ := HolderAuxDeferred.drained_empty hi flag drain
    have actual := (RxHistory.mixed_erases (requireDrainedPrefix_erases _ _) w h).symm.trans (congrArg Prod.fst drain)
    have same := (requireDrained_normal _ _ w u actual).1
    have account : Boundary [] loans w.wg := by
      obtain ⟨prior,priorEq,boundary⟩ := hi.1.1
      have samePrior : prior=suffix := List.append_cancel_left (priorEq.symm.trans hist)
      simpa only [samePrior,empty] using boundary
    have accountOut : Boundary [] loans u.wg := by simpa only [same] using account
    have atCut := HolderInitial.at_cut accountOut post.1.2 post.2.1 post.2.2
    have tailHistory : k=j := by simpa only [runPrefix_lift] using (congrArg Prod.snd tail).symm
    subst k
    have kept := (ProjectedAction.iff_run _ _ _).mp deliverSent_sameKernel u () v (congrArg Prod.fst tail)
    have dev : v.wg.dev=u.wg.dev := congrArg (fun p : ProductStore43 => p.2.2.2.dev) kept
    exact ⟨suffix,hist,empty,HolderAuxiliary.store atCut kept,
      fun d id packet hv => noPackets d id packet (dev ▸ hv)⟩

/-- The record-mode entry takes the actual guarded branch. The theorem uses
no queue-empty, completed-callback or output-funding hypothesis. -/
theorem recorded_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (recorded : w.ambient.hidden.isSome=true)
    (run : runPrefix RxHistory.afterBatch w h=(.ok ((),v),k)) :
    HolderAuxiliary.Inv [] loans k k v ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket), v.wg.dev=some d → d.rxSkbs[id]?≠some packet) := by
  rw [source_factor] at run
  let start : World := {w with wg:={w.wg with queuedThisCall:=[]}}
  have present : w.ambient.hidden.isNone=false := by cases hh:w.ambient.hidden <;> simp_all
  change (runPrefix (if w.ambient.hidden.isNone then
    RxHistory.runCryptWorkers >>= fun _ => RxHistory.runSendWorkers else wait >>= fun _ => finish) start h)=_ at run
  simp only [present,Bool.false_eq_true,ite_false] at run
  have entry : HolderAuxiliary.Inv initial loans before h start := HolderAuxiliary.store hi rfl
  obtain ⟨x,u,j,work,done⟩ := DecryptIteration.bind_normal run
  cases x
  have after := (wait_preserves initial loans before start h entry).choose_spec.2.2
  rw [work] at after
  obtain ⟨_,_,_,account,empty⟩ := finish_normal after done
  exact ⟨account,empty⟩

end Leanux.Proofs.WG.Queues.RxCredits.AfterBatchCompletion
