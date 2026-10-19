import Leanux.Proofs.WG.Progress.EncryptSuffixSource
import Leanux.Proofs.WG.Progress.DecryptStepSuffixSource
import Leanux.Proofs.WG.Progress.ActivationRecordSource

/-! Actual worker iterations retain supplied-record suffixes and strictly
consume on yield. The existing activation loop then gives strict decrease on
normal return, conditional only on the separate NAPI/IRQ suffix obligations.
This is partial correctness, not successful evaluation or global termination. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Noise Queues

theorem condResched_after_tail (worker : Worker) (records : List HiddenRecord) :
    Hoare (condResched worker) (fun w=>Tail records w.ambient.hidden)
      (fun yielded w=>Tail records w.ambient.hidden ∧
        (yielded=true→StrictTail records w.ambient.hidden)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w yielded v pre run
  obtain ⟨middle,present,prior⟩:=pre
  have result:=(hoare_iff_run _ _ _).mp (condResched_suffix worker middle) w yielded v present run
  exact ⟨tail_extend prior result.1,fun h=>strict_extend prior (result.2 h)⟩

theorem rescheduleBranch_after_tail (worker : Worker) (site : Decision) (records : List HiddenRecord) :
    Hoare (do branch site (←condResched worker) : Leanux.M Bool)
      (fun w=>Tail records w.ambient.hidden)
      (fun yielded w=>Tail records w.ambient.hidden ∧
        (yielded=true→StrictTail records w.ambient.hidden)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w yielded v pre run
  rw [StateT.run_bind] at run
  cases choice : (condResched worker).run w with
  | error e => rw [choice] at run; cases run
  | ok pair =>
    obtain ⟨value,middle⟩:=pair
    have result:=(hoare_iff_run _ _ _).mp (condResched_after_tail worker records)
      w value middle pre choice
    rw [choice] at run
    cases run
    exact result

theorem workerIter_record_effect (worker : Worker) (pid : Option Nat)
    (step afterItem : Leanux.M Bool) (records : List HiddenRecord)
    (stepKeeps : Preserves (fun w : World=>Tail records w.ambient.hidden) step)
    (afterKeeps : Hoare afterItem (fun w=>Tail records w.ambient.hidden)
      (fun yielded w=>Tail records w.ambient.hidden ∧
        (yielded=true→StrictTail records w.ambient.hidden))) :
    Hoare (workerIter worker pid step afterItem)
      (fun w=>w.ambient.hidden=some records)
      (fun result w=>Tail records w.ambient.hidden ∧
        (result=.yielded→StrictTail records w.ambient.hidden)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v present run
  unfold workerIter at run
  rw [StateT.run_bind] at run
  cases first : step.run w with
  | error e => rw [first] at run; cases run
  | ok pair =>
    obtain ⟨consumed,middle⟩:=pair
    have kept:=(hoare_iff_run _ _ _).mp stepKeeps w consumed middle
      (present ▸ tail_self records) first
    rw [first] at run
    cases consumed with
    | false =>
      cases run
      exact ⟨kept,by intro bad; cases bad⟩
    | true =>
      change (afterItem.run middle >>= _) = .ok (result,v) at run
      cases next : afterItem.run middle with
      | error e => rw [next] at run; cases run
      | ok pair =>
        obtain ⟨yielded,last⟩:=pair
        have post:=(hoare_iff_run _ _ _).mp afterKeeps middle yielded last kept next
        rw [next] at run
        cases yielded with
        | false =>
          cases run
          exact ⟨post.1,by intro bad; cases bad⟩
        | true =>
          cases run
          exact ⟨post.1,fun _=>post.2 rfl⟩

theorem encryptIteration_record_effect (records : List HiddenRecord) (softirq : Leanux.M Unit)
    (softKeeps : Preserves (fun w : World=>Tail records w.ambient.hidden) softirq) :
    Hoare (encryptIter Env.checksumHelp softirq (condResched .encryptWorker))
      (fun w=>w.ambient.hidden=some records)
      (fun result w=>Tail records w.ambient.hidden ∧
        (result=.yielded→StrictTail records w.ambient.hidden)) :=
  workerIter_record_effect _ _ _ _ records (encryptStep_retains records softirq softKeeps)
    (rescheduleBranch_after_tail _ _ records)

theorem decryptIteration_record_effect (records : List HiddenRecord) (softirq irq : Leanux.M Unit)
    (softKeeps : Preserves (fun w : World=>Tail records w.ambient.hidden) softirq)
    (irqKeeps : Preserves (fun w : World=>Tail records w.ambient.hidden) irq) :
    Hoare (decryptIter softirq irq (condResched .decryptWorker))
      (fun w=>w.ambient.hidden=some records)
      (fun result w=>Tail records w.ambient.hidden ∧
        (result=.yielded→StrictTail records w.ambient.hidden)) :=
  workerIter_record_effect _ _ _ _ records (decryptStep_retains records softirq irq softKeeps irqKeeps)
    (rescheduleBranch_after_tail _ _ records)

theorem encrypt_activation_strict
    (softKeeps : ∀ records,Preserves (fun w : World=>Tail records w.ambient.hidden) Env.napiSoftirq)
    (a : Activation) (worker : a.worker=.encryptWorker) (records : List HiddenRecord) :
    Hoare (Activation.run a) (fun w=>w.ambient.hidden=some records)
      (fun _ w=>StrictTail records w.ambient.hidden) := by
  apply activation_strict_of_iterations .encryptWorker _ a worker records
  intro active same input
  simpa only [Activation.iter,same] using encryptIteration_record_effect input Env.napiSoftirq (softKeeps input)

theorem decrypt_activation_strict
    (softKeeps : ∀ records,Preserves (fun w : World=>Tail records w.ambient.hidden) Env.napiSoftirq)
    (irqKeeps : ∀ records,Preserves (fun w : World=>Tail records w.ambient.hidden) Env.napiIrqExit)
    (a : Activation) (worker : a.worker=.decryptWorker) (records : List HiddenRecord) :
    Hoare (Activation.run a) (fun w=>w.ambient.hidden=some records)
      (fun _ w=>StrictTail records w.ambient.hidden) := by
  apply activation_strict_of_iterations .decryptWorker _ a worker records
  intro active same input
  simpa only [Activation.iter,same] using
    decryptIteration_record_effect input Env.napiSoftirq Env.napiIrqExit (softKeeps input) (irqKeeps input)

end Leanux.Proofs.WG.Progress.RecordSuffix
