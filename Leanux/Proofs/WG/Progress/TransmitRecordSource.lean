import Leanux.Proofs.WG.Progress.TxWorkerSuffixSource
import Leanux.Proofs.WG.Progress.NapiSuffixConcreteSource
import Leanux.Proofs.WG.Progress.ClearWorkerRecordFrames
import Leanux.Proofs.Framing.EnvOperations

/-! The original transmit activation, including its cryptAhead prelude. All
callbacks are concrete. Normal return strictly consumes supplied records; no
successful evaluation or global progress is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.TimerDiscipline Leanux.Proofs.WG.Noise Queues

theorem txIteration_record_effect (records : List HiddenRecord) (pid : PeerId) :
    Hoare (txIter pid (Env.condResched .txWorker))
      (fun w=>w.ambient.hidden=some records)
      (fun result w=>Tail records w.ambient.hidden ∧
        (result=.yielded→StrictTail records w.ambient.hidden)) :=
  workerIter_record_effect _ _ _ _ records
    (native_product records _ (txStep_retains records pid))
    (rescheduleBranch_after_tail _ _ records)

theorem cryptAhead_retains (records : List HiddenRecord) (pid : PeerId) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.cryptAhead pid) := by
  have getA : Preserves (fun w : World=>Tail records w.ambient.hidden)
      (getAmbient : Leanux.M Ambient) :=
    native_product records _ (native_getAmbient records)
  have getP (p : PeerId) : Preserves (fun w : World=>Tail records w.ambient.hidden)
      (getPeer p : Leanux.M Peer) := native_product records _ (native_getPeer records p)
  have getT (id : SkbId) : Preserves (fun w : World=>Tail records w.ambient.hidden)
      (getTxSkb id : Leanux.M DataPacket) := native_product records _ (native_getTx records id)
  have modifyD (f : Device→Device) : Preserves (fun w : World=>Tail records w.ambient.hidden)
      (modifyDev f : Leanux.M Unit) := native_product records _ (native_modifyDev records f)
  have stop {α : Type} (e : Stop) :
      Preserves (fun w : World=>Tail records w.ambient.hidden) (throw e : Leanux.M α) :=
    hoare_throw e
  unfold Env.cryptAhead
  repeat' first
    | env_operation_fact getA
    | env_operation_fact getP
    | env_operation_fact getT
    | env_operation_fact modifyD
    | env_operation_fact peek_retains
    | (env_operation_fact encryptIteration_retains; exact softirq_retains records)
    | (env_operation_fact modifyAmbient_hidden; intro; rfl)
    | env_operation_fact product_invariant_retains
    | env_operation_fact stop
    | env_operation_fact preserves_bind
    | env_operation_fact preserves_pure
    | env_operation_step

theorem txIteration_after_tail (records : List HiddenRecord) (pid : PeerId) :
    Hoare (txIter pid (Env.condResched .txWorker))
      (fun w=>Tail records w.ambient.hidden)
      (fun result w=>Tail records w.ambient.hidden ∧
        (result=.yielded→StrictTail records w.ambient.hidden)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  obtain ⟨rest,present,prior⟩:=pre
  have post:=(hoare_iff_run _ _ _).mp (txIteration_record_effect rest pid)
    w result v present run
  exact ⟨tail_extend prior post.1,fun h=>strict_extend prior (post.2 h)⟩

theorem txActivation_iteration (a : Activation) (same : a.worker=.txWorker)
    (records : List HiddenRecord) :
    Hoare (Env.Activation.iter a) (fun w=>w.ambient.hidden=some records)
      (fun result w=>Tail records w.ambient.hidden ∧
        (result=.yielded→StrictTail records w.ambient.hidden)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  simp only [Env.Activation.iter,same] at run
  cases hp : a.pid with
  | none => rw [hp] at run; cases run
  | some pid =>
    rw [hp,StateT.run_bind] at run
    cases first : (Env.cryptAhead pid).run w with
    | error error => rw [first] at run; cases run
    | ok pair =>
      obtain ⟨value,middle⟩:=pair
      rw [first] at run
      have kept:=(hoare_iff_run _ _ _).mp (cryptAhead_retains records pid)
        w value middle (pre ▸ tail_self records) first
      exact (hoare_iff_run _ _ _).mp (txIteration_after_tail records pid)
        middle result v kept run

theorem txActivation_strict (a : Activation) (worker : a.worker=.txWorker)
    (records : List HiddenRecord) :
    Hoare (Env.Activation.run a) (fun w=>w.ambient.hidden=some records)
      (fun _ w=>StrictTail records w.ambient.hidden) :=
  activation_strict_of_iterations .txWorker txActivation_iteration a worker records

end Leanux.Proofs.WG.Progress.RecordSuffix
