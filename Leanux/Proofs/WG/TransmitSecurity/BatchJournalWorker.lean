import Leanux.Proofs.WG.TransmitSecurity.BatchJournalFrames

/-! The actual encryption continuation appends head/packet key agreement
from its selected coherent batch. Partial prefixes remain checked on Stop. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

private theorem local_tail (item : Option (List SkbId)) :
    PrefixEnsures (fun h (w : World) => BatchCoherence.Native.Coherent [] item.toList w.wg ∧ BatchWorkerHistory.Good h)
      BatchWorkerHistory.Good (WorkerEncryption.tail item)
      (fun _ h _ => BatchWorkerHistory.Good h) := by
  cases item with
  | none =>
    unfold WorkerEncryption.tail
    apply PrefixEnsures.bind
    · exact PrefixEnsures.lift _ (fun _ _ hi => hi.2)
        (fun _ _ _ _ hi _ => hi.2)
    · intro _
      exact PrefixEnsures.pure (fun _ _ hi => hi) (fun _ _ hi => hi)
  | some items =>
    intro w h before
    obtain ⟨pid,slot,aligned⟩ := BatchCoherence.selected before.1.2 before.1.1
    obtain ⟨suffix,extension,good,_⟩ := BatchWorkerHistory.tail w h ⟨aligned,before.2⟩
    refine ⟨suffix,extension,good,?_⟩
    cases (runPrefix (WorkerEncryption.tail (some items)) w h).1 <;> trivial

private theorem focused (item : Option (List SkbId)) :
    PrefixEnsures (Inv item.toList) Safe
      (focusPrefix Journal.Event.encrypted Journal.encryption? (WorkerEncryption.tail item))
      (fun _ h _ => Safe h) :=
  (local_tail item).focus Journal.Event.encrypted Journal.encryption? (fun _ => rfl)

private theorem return_receipt (item : Option (List SkbId)) (r : RunWitness Bool) :
    PrefixPreserves (fun h (_ : World) => Safe h) Safe (emitPrefix (.encryptionReturn item r)) := by
  intro w h before
  simp only [runPrefix_emit]
  have same : receipts (h ++ [Journal.Event.encryptionReturn item r]) = receipts h := by
    simp only [receipts,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      Journal.encryption?,List.append_nil]
  exact ⟨[.encryptionReturn item r],rfl,before.frame same,before.frame same⟩

theorem hook (item : Option (List SkbId)) :
    PrefixEnsures (Inv item.toList) Safe (Journal.encrypt item) (fun _ h _ => Safe h) := by
  unfold Journal.encrypt receiptObserved
  apply PrefixEnsures.bind (PrefixEnsures.captureObserved (focused item))
  intro r w h before
  rw [← before.1]
  exact PrefixPreserves.bind (return_receipt item r)
    (fun _ => PrefixPreserves.pure (I := fun h (_ : World) => Safe h)
      (fun _ _ hi => hi) r.value) r.after h before.2.1

private theorem resched : PrefixPreserves (fun h (_ : World) => Safe h) Safe
    (Driver.reschedObserved .encryptWorker .encWorkerNeedResched) := by
  unfold Driver.reschedObserved
  have lift_safe {α : Type} (a : Leanux.M α) : PrefixPreserves (fun h (_ : World) => Safe h) Safe (liftPrefix a) :=
    (PrefixEnsures.lift (P := fun h (_ : World) => Safe h) (S := Safe)
      (Q := fun (_ : α) h (_ : World) => Safe h) a
      (fun _ _ hi => hi) (fun _ _ _ _ hi _ => hi)).preserves
  apply PrefixPreserves.bind (lift_safe (Env.condResched .encryptWorker))
  intro yes
  exact lift_safe _

private theorem tail_history (item : Option (List SkbId)) :
    PrefixEnsures (Inv item.toList) Safe (Driver.encryptTailObserved Journal.hooks item)
      (fun _ h _ => Safe h) := by
  unfold Driver.encryptTailObserved workerIterPrefix
  apply PrefixEnsures.bind (hook item)
  intro more
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi) (fun _ _ hi => hi)
  · change PrefixPreserves (fun h (_ : World) => Safe h) Safe _
    apply PrefixPreserves.bind resched
    intro yes
    exact PrefixPreserves.pure (I := fun h (_ : World) => Safe h) (fun _ _ hi => hi) _

theorem tail (item : Option (List SkbId)) :
    PrefixEnsures (Inv item.toList) Safe (Driver.encryptTailObserved Journal.hooks item)
      (fun _ => Inv []) := by
  intro w h before
  obtain ⟨suffix,extension,safe,_⟩ := tail_history item w h before
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix (Driver.encryptTailObserved Journal.hooks item) w h).1 with
  | error stop => trivial
  | ok out =>
    have projected := Driver.encryptTail_projects Journal.hooks_projects item
    rw [Driver.nonce_encryptTailObserved_eq] at projected
    have erased : ErasesPrefix (Nonce.encryptTailObserved item) (RxWorkers.encryptTailSource item) :=
      workerIterPrefix_erases _ _ (erasesPrefix_lift _) (Nonce.reschedObserved_erases _ _)
    have native := DriverOwnership.product_native projected erased w out.2 h result
    exact ⟨BatchCoherence.Encrypt.tail (by simpa only [List.append_nil] using before.1) native,safe⟩

theorem iteration : PrefixPreserves (Inv []) Safe (Driver.encryptIterObserved Journal.hooks) := by
  unfold Driver.encryptIterObserved
  change PrefixEnsures (Inv []) Safe (Journal.poll >>= _) (fun _ => Inv [])
  apply PrefixEnsures.bind poll
  intro item
  simp only [List.append_nil]
  apply PrefixEnsures.bind (softirq (active := item.toList))
  intro _
  exact tail item

end Leanux.Proofs.WG.TransmitSecurity.BatchJournal
