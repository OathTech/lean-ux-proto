import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistoryFrames
import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistoryPoll
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastWorker

/-! The actual encryption tail extends historical exclusion. Its partial
prefix remains nonrepeating on Stop; normal completion restores physical
ownership using the same native tail, including its reschedule suffix. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

def Past (active : List (List SkbId)) (h : List Journal.Event) (w : World) : Prop :=
  EncryptionPast.Inv (used h) active (EncryptionPast.view w.wg)

private theorem local_tail (item : Option (List SkbId)) :
    PrefixEnsures (fun h (w : World) => Native (h.map WorkerEpochs.identity) (item.toList ++ active) w.wg)
      (fun h => (h.map WorkerEpochs.identity).Nodup) (WorkerEncryption.tail item)
      (fun _ h w => EncryptionPast.Inv (h.map WorkerEpochs.identity) active (EncryptionPast.view w.wg)) := by
  cases item with
  | none =>
    have quiet : PrefixEnsures
        (fun h (w : World) => Native (h.map WorkerEpochs.identity) active w.wg)
        (fun h => (h.map WorkerEpochs.identity).Nodup)
        (liftPrefix (branch .encWorkerConsumed false))
        (fun _ h (w : World) => Native (h.map WorkerEpochs.identity) active w.wg) := by
      apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.2.1)
      intro h w result v before run
      exact (hoare_iff_run _ _ _).mp
        (productAmbient_spec (AmbientM.branch .encWorkerConsumed false)
          (fun w : World => Native (h.map WorkerEpochs.identity) active w.wg)
          (fun _ _ hi => hi)) w result v before run
    unfold WorkerEncryption.tail
    simp only [Option.toList_none,List.nil_append]
    apply PrefixEnsures.bind quiet
    intro _
    exact PrefixEnsures.pure (fun _ _ hi => hi.1.2.1) (fun _ _ hi => hi.1.2)
  | some items =>
    intro w h before
    obtain ⟨suffix,extension,_,_⟩ := WorkerEpochs.tail_suffix (some items) w h
    refine ⟨suffix,extension,(EncryptionPast.worker before.2 before.1.2).1,?_⟩
    cases result : (runPrefix (WorkerEncryption.tail (some items)) w h).1 with
    | error stop => trivial
    | ok out => exact (EncryptionPast.worker before.2 before.1.2).2 out.1 out.2 result

private theorem focused (item : Option (List SkbId)) :
    PrefixEnsures (Inv (item.toList ++ active)) Safe
      (focusPrefix Journal.Event.encrypted Journal.encryption? (WorkerEncryption.tail item))
      (fun _ => Past active) :=
  (local_tail item).focus Journal.Event.encrypted Journal.encryption? (fun _ => rfl)

private theorem return_receipt (item : Option (List SkbId)) (r : RunWitness Bool) :
    PrefixPreserves (Past active) Safe (emitPrefix (.encryptionReturn item r)) := by
  intro w h before
  simp only [runPrefix_emit]
  have same : used (h ++ [Journal.Event.encryptionReturn item r]) = used h := by
    simp only [used,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      Journal.encryption?,List.append_nil]
  exact ⟨[.encryptionReturn item r],rfl,by simpa only [Safe,same] using before.1,
    by simpa only [Past,same] using before⟩

theorem hook (item : Option (List SkbId)) :
    PrefixEnsures (Inv (item.toList ++ active)) Safe (Journal.encrypt item) (fun _ => Past active) := by
  unfold Journal.encrypt receiptObserved
  apply PrefixEnsures.bind (PrefixEnsures.captureObserved (focused item))
  intro r w h before
  rw [← before.1]
  exact PrefixPreserves.bind (return_receipt item r)
    (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.1) r.value) r.after h before.2.1

private theorem past_resched : PrefixPreserves (Past active) Safe
    (Driver.reschedObserved .encryptWorker .encWorkerNeedResched) := by
  have cond : PrefixPreserves (Past active) Safe (liftPrefix (Env.condResched .encryptWorker)) := by
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
    intro h w result v before run
    have same := (ProjectedAction.iff_run _ _ _).mp (condResched_sameKernel .encryptWorker) w result v run
    have device := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
    have epochs := congrArg (fun s : ProductStore43 => s.2.2.2.netIfindexNext) same
    change v.wg.dev = w.wg.dev at device
    change v.wg.netIfindexNext = w.wg.netIfindexNext at epochs
    simpa only [Past,EncryptionPast.view,device,epochs] using before
  unfold Driver.reschedObserved
  apply PrefixPreserves.bind cond
  intro yes
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w result v before run
  cases run
  exact before

private theorem tail_past (item : Option (List SkbId)) :
    PrefixEnsures (Inv (item.toList ++ active)) Safe (Driver.encryptTailObserved Journal.hooks item)
      (fun _ => Past active) := by
  unfold Driver.encryptTailObserved workerIterPrefix
  apply PrefixEnsures.bind (hook item)
  intro more
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind past_resched
    intro yes
    exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)

theorem tail (item : Option (List SkbId)) :
    PrefixEnsures (Inv item.toList) Safe (Driver.encryptTailObserved Journal.hooks item)
      (fun _ => Inv []) := by
  intro w h before
  obtain ⟨suffix,extension,safe,post⟩ := tail_past (active := []) item w h
    (by simpa only [List.append_nil] using before)
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix (Driver.encryptTailObserved Journal.hooks item) w h).1 with
  | error stop => trivial
  | ok out =>
    have projected := Driver.encryptTail_projects Journal.hooks_projects item
    rw [Driver.nonce_encryptTailObserved_eq] at projected
    have erased : ErasesPrefix (Nonce.encryptTailObserved item) (RxWorkers.encryptTailSource item) :=
      workerIterPrefix_erases _ _ (erasesPrefix_lift _) (Nonce.reschedObserved_erases _ _)
    have native := DriverOwnership.product_native projected erased w out.2 h result
    exact ⟨⟨(hoare_iff_run _ _ _).mp (TxDisposition.LiveWorkers.encrypt_tail item)
      w out.1 out.2 before.1.1 native,by simpa only [result,Past] using post⟩,
      OccurrenceEncrypt.tail (by simpa only [List.append_nil] using before.2) native⟩

theorem iteration : PrefixPreserves (Inv []) Safe (Driver.encryptIterObserved Journal.hooks) := by
  unfold Driver.encryptIterObserved
  change PrefixEnsures (Inv []) Safe (Journal.poll >>= _) (fun _ => Inv [])
  apply PrefixEnsures.bind poll
  intro item
  simp only [List.append_nil]
  apply PrefixEnsures.bind (softirq (active := item.toList))
  intro _
  exact tail item

end Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory
