import Leanux.Proofs.WG.Queues.RunnerInitialSelection
import Leanux.Proofs.WG.Queues.RunnerOperationSelection

/-! Initialization exposes the same normal continuation certificate selected
by the original prefill and boot source. Failed initialization cannot provide
a normal certificate. These are projections, not another execution. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerInitializedCuts
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open AdmissionSelection RunnerSelectionData

theorem prefill_cut (count : Nat) (w : World) (next : World → PrefixOuter RxHistory.Event α)
    (checked : ∀ v, wgStoreView v.wg = wgStoreView w.wg → ConservationCertified.Certified (next v) P Q)
    (selected : ∀ v same, Selection (checked v same).rule)
    (source : (ConservationRunner.prefillCertified count w next checked).rule.relation cs h out k final) :
    ∃ v same, runPrefixOuter (ConservationRunner.prefillWith count w (pure : World → PrefixOuter RxHistory.Event World)) h = (.ok v,h) ∧
      ∃ continuation : (checked v same).rule.relation cs h out k final,
      ∀ operation inner c, (selected v same).query operation inner continuation c →
        (RunnerSelection.prefill count w next checked selected).query operation inner source c := by
  unfold ConservationRunner.prefillCertified at source
  split at source
  · rename_i positive
    split at source
    · rename_i result actual
      refine ⟨{ w with seccomp := result.1, tasks := result.2 },rfl,?_,source,?_⟩
      · simp only [ConservationRunner.prefillWith,positive,actual,↓reduceIte]
        rfl
      · intro operation inner c chosen
        dsimp only [RunnerSelection.prefill]
        rw [ite_eq_left positive,actual]
        exact ⟨rfl,source,chosen⟩
    · exact False.elim source
  · rename_i negative
    refine ⟨w,rfl,?_,source,?_⟩
    · simp only [ConservationRunner.prefillWith,negative,↓reduceIte]
      rfl
    · intro operation inner c chosen
      dsimp only [RunnerSelection.prefill]
      rw [ite_eq_right negative]
      exact ⟨source,chosen⟩

theorem boot_cut (net foreign : Bool) (w : World) (next : World → PrefixOuter RxHistory.Event α)
    (checked : ∀ v, wgStoreView v.wg = wgStoreView w.wg → ConservationCertified.Certified (next v) P Q)
    (selected : ∀ v same, Selection (checked v same).rule)
    (source : (ConservationRunner.bootCertified net foreign w next checked).rule.relation cs h out k final) :
    ∃ v same, runPrefixOuter (ConservationRunner.bootWith net foreign w (pure : World → PrefixOuter RxHistory.Event World)) h = (.ok v,h) ∧
      ∃ continuation : (checked v same).rule.relation cs h out k final,
      ∀ operation inner c, (selected v same).query operation inner continuation c →
        (RunnerSelection.boot net foreign w next checked selected).query operation inner source c := by
  unfold ConservationRunner.bootCertified at source
  split at source
  · rename_i enabled
    split at source
    · rename_i result actual
      have frame : SameView (fun w : World => wgStoreView w.wg)
          (do Net.Fib.bootTables; if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit) := by
        apply SameView.bind
        · intro initial
          exact productRouting_spec _ (fun s=>s.2.2.2=initial)
        · intro _
          split
          · intro initial
            exact productRouting_spec _ (fun s=>s.2.2.2=initial)
          · exact SameView.pure _ _
      have same := (Lifetimes.ProjectedAction.iff_run _ _ _).mp frame w result.1 result.2 actual
      refine ⟨{ result.2 with ambient := { result.2.ambient with steps := #[], envCalls := [] } },same,?_,source,?_⟩
      · simp only [ConservationRunner.bootWith,enabled,actual,↓reduceIte]
        rfl
      · intro operation inner c chosen
        dsimp only [RunnerSelection.boot]
        rw [ite_eq_left enabled,actual]
        exact ⟨same,source,chosen⟩
    · exact False.elim source
  · rename_i disabled
    refine ⟨w,rfl,?_,source,?_⟩
    · simp only [ConservationRunner.bootWith,disabled]
      rfl
    · intro operation inner c chosen
      dsimp only [RunnerSelection.boot]
      rw [ite_eq_right disabled]
      exact ⟨source,chosen⟩

/-- The tail World is obtained by the actual prefill and boot prefix, with
unchanged incoming history; the query lift applies to every chosen carrier. -/
theorem initialized_cut (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (queries : ∀c,Nat→Query (rules c))
    (chosen : ∀c inner,Fates (queries c inner))
    (effects : ∀c,ConservationEffects.Conserves (rules c))
    (trace : Trace) (placeholders : Bool)
    (source : (ConservationRunner.initialized call rules established trace placeholders).rule.relation cs h out k final) :
    ∃ u v,
      runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
        (ConservationRunner.fixture trace placeholders) (pure : World → PrefixOuter RxHistory.Event World)) h = (.ok u,h) ∧
      runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
        (pure : World → PrefixOuter RxHistory.Event World)) h = (.ok v,h) ∧
      ∃ continuation : (ConservationRunner.tail call rules established trace v).rule.relation cs h out k final,
        ∀ operation inner c,
          (RunnerSelection.tail call rules established queries chosen effects trace v).query operation inner continuation c →
          (RunnerSelection.initialized call rules established queries chosen effects trace placeholders).query operation inner source c := by
  obtain ⟨u,preStore,preRun,preSource,preLift⟩ :=
    prefill_cut trace.seccompPrefill (ConservationRunner.fixture trace placeholders) _ _
      (fun u preStore => RunnerSelection.boot trace.net trace.foreign u _
        (fun v bootStore => ConservationRunner.initialTail call rules established trace v (bootStore.trans preStore))
        (fun v _ => RunnerSelection.tail call rules established queries chosen effects trace v)) source
  obtain ⟨v,bootStore,bootRun,tailSource,bootLift⟩ :=
    boot_cut trace.net trace.foreign u _ _
      (fun v _ => RunnerSelection.tail call rules established queries chosen effects trace v) preSource
  refine ⟨u,v,preRun,bootRun,tailSource,?_⟩
  intro operation inner c selected
  exact preLift operation inner c (bootLift operation inner c selected)

/-- Every bounded original operation has its actual initialized source cut,
independently of any selected admission. The final universal lift includes
admissions removed before this runner returns. -/
theorem account_cut (trace : Trace) (placeholders : Bool) {cs h out k final index}
    (source : (RunnerAccount.rule trace placeholders).relation cs h out k final)
    (bound : index < trace.ops.size) :
    ∃ u v op before j incoming ret returned received admitted,
      runPrefixOuter (ConservationRunner.prefillWith trace.seccompPrefill
        (ConservationRunner.fixture trace placeholders) (pure : World → PrefixOuter RxHistory.Event World)) h = (.ok u,h) ∧
      runPrefixOuter (ConservationRunner.bootWith trace.net trace.foreign u
        (pure : World → PrefixOuter RxHistory.Event World)) h = (.ok v,h) ∧
      trace.ops.toList[index]? = some op ∧ before.2.1.size = index ∧
      runPrefixOuter (forIn (trace.ops.toList.take index) (v,#[],#[],#[],#[],#[])
        (RunnerOperation.operation RxHistory.syscall trace)) h = (.ok before,j) ∧
      ∃ front : (ConservationSyscall.rule (toSyscall before.2.1 before.2.2.1 before.2.1.size op)).relation
        incoming (RunnerOperation.prepare trace before) j ret returned received admitted,
        ∀ inner c, SyscallSelection.syscall _ inner front c →
          (RunnerSelection.account trace placeholders).query index inner source c := by
  obtain ⟨u,v,preRun,bootRun,tailSource,initLift⟩ := initialized_cut
    RxHistory.syscall ConservationSyscall.rule ConservationSyscall.established
    SyscallSelection.syscall SyscallSelection.syscall_fates SyscallEffects.syscall
    trace placeholders source
  obtain ⟨op,before,j,incoming,ret,returned,received,admitted,position,indexEq,prior,front,tailLift⟩ :=
    RunnerOperationSelection.tail_cut RxHistory.syscall ConservationSyscall.rule
      ConservationSyscall.established SyscallSelection.syscall
      SyscallSelection.syscall_fates SyscallEffects.syscall trace v tailSource bound
  refine ⟨u,v,op,before,j,incoming,ret,returned,received,admitted,
    preRun,bootRun,position,indexEq,prior,front,?_⟩
  intro inner c selected
  exact initLift index inner c (tailLift inner c selected)

end Leanux.Proofs.WG.Queues.RxCredits.RunnerInitializedCuts
