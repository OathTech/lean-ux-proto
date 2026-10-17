import Leanux.Proofs.WG.Queues.RunnerTailSelection
import Leanux.Proofs.WG.Queues.RunnerOperationCuts
import Leanux.Proofs.WG.Queues.RunnerSelectionCuts

/-! Every bounded position of the original normal runner loop has an actual
source certificate. The extraction does not select a carrier or require it to
survive. Selection at that independently exposed cut lifts through the existing
query, including admissions removed before the whole runner returns. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerOperationSelection
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open AdmissionSelection RunnerSelectionData

/-- Project a numeric body occurrence from an existing finite-loop certificate.
The supplied yield fact describes the actual body source; no execution is added. -/
theorem list_cut (items : List γ) (initial : β)
    (action : γ → β → PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀ item acc, ConservationOuter.Rule (action item acc))
    (selected : ∀ item acc, Selection (rules item acc))
    (yields : ∀ item acc {cs h step j next},
      (rules item acc).relation cs h step j next → ∃ out, step = .yield out)
    {cs h result k final index}
    (source : (ConservationOuter.forIn items initial action rules).relation cs h result k final)
    (bound : index < items.length) :
    ∃ item before after j l middle next,
      items[index]? = some item ∧
      (ConservationOuter.forIn (items.take index) initial action rules).relation cs h before j middle ∧
      ∃ body : (rules item before).relation middle j (.yield after) l next,
        (ConservationOuter.forIn (items.drop (index+1)) after action rules).relation next l result k final ∧
        ∀ position inner c, (selected item before).query position inner body c →
          (RunnerSelectionData.forIn items initial action rules selected).query position inner source c := by
  induction items generalizing initial cs h index with
  | nil => simp at bound
  | cons item items ih =>
    obtain ⟨step,j,middle,front,rest⟩ := source
    obtain ⟨acc,rfl⟩ := yields item initial front
    cases index with
    | zero =>
      refine ⟨item,initial,acc,h,j,cs,middle,rfl,⟨rfl,rfl,rfl⟩,front,rest,?_⟩
      intro position inner c chosen
      exact RunnerSelectionCuts.forIn_here item items initial action rules selected
        ⟨.yield acc,j,middle,front,rest⟩ front chosen
    | succ index =>
      obtain ⟨item',before,after,l,m,middle',next,atIndex,prior,body,suffix,lifted⟩ :=
        ih acc rest (Nat.lt_of_succ_lt_succ bound)
      refine ⟨item',before,after,l,m,middle',next,atIndex,?_,body,suffix,?_⟩
      · exact ⟨.yield acc,j,middle,front,prior⟩
      · intro position inner c chosen
        exact RunnerSelectionCuts.forIn_later item items initial action rules selected
          ⟨.yield acc,j,middle,front,rest⟩
          front rest (lifted position inner c chosen)

/-- Selection in the exact syscall cut of an operation needs no premise about
its later guards or metadata loops. The parent certificate supplies that tail. -/
theorem operation_selected (call : Syscall → RxHistory.Obs Int)
    (rules : ∀ c, ConservationSource.Rule (call c))
    (established : ∀ c, HolderTrafficDispatch.Established (rules c) [])
    (queries : ∀ c, Nat → Query (rules c))
    (chosen : ∀ c inner, Fates (queries c inner))
    (effects : ∀ c, ConservationEffects.Conserves (rules c))
    (trace : Trace) (op : Operation) (state : RunnerOperation.State)
    (source : (ConservationRunner.operationCertified call rules established trace op state).rule.relation
      cs h step k final)
    (front : (rules (toSyscall state.2.1 state.2.2.1 state.2.1.size op)).relation
      cs (RunnerOperation.prepare trace state) h ret returned j middle)
    (selection : queries _ inner front c) :
    (RunnerSelection.operation call rules established queries chosen effects trace op state).query
      state.2.1.size inner source c := by
  exact RunnerSelectionCuts.bind_left (x := (ret,returned)) (j := j) (middle := middle)
    (RunnerSelectionData.runAt state.2.1.size (RunnerOperation.prepare trace state)
      (rules _) (queries _) (chosen _) (effects _))
    (fun out => RunnerSelection.afterCall op state out.1 out.2) source front ⟨rfl,selection⟩

/-- Every operation of the original normal tail exposes its exact syscall
certificate before any carrier is selected. A selection at that cut lifts to
the complete tail, regardless of whether later calls remove the carrier. -/
theorem tail_cut (call : Syscall → RxHistory.Obs Int)
    (rules : ∀ c, ConservationSource.Rule (call c))
    (established : ∀ c, HolderTrafficDispatch.Established (rules c) [])
    (queries : ∀ c, Nat → Query (rules c))
    (chosen : ∀ c inner, Fates (queries c inner))
    (effects : ∀ c, ConservationEffects.Conserves (rules c))
    (trace : Trace) (w : World) {cs h out k final index}
    (source : (ConservationRunner.tail call rules established trace w).rule.relation cs h out k final)
    (bound : index < trace.ops.size) :
    ∃ op before j incoming ret returned received admitted,
      trace.ops.toList[index]? = some op ∧ before.2.1.size = index ∧
      runPrefixOuter (forIn (trace.ops.toList.take index) (w,#[],#[],#[],#[],#[])
        (RunnerOperation.operation call trace)) h = (.ok before,j) ∧
      ∃ front : (rules (toSyscall before.2.1 before.2.2.1 before.2.1.size op)).relation
        incoming (RunnerOperation.prepare trace before) j ret returned received admitted,
        ∀ inner c, queries _ inner front c →
          (RunnerSelection.tail call rules established queries chosen effects trace w).query
            index inner source c := by
  let body := fun op acc => (ConservationRunner.operationCertified call rules established trace op acc).rule
  let selected := RunnerSelection.operation call rules established queries chosen effects trace
  have completeSource := source
  obtain ⟨complete,done,completed,loop,finish⟩ := completeSource
  have boundList : index < trace.ops.toList.length := by simpa using bound
  have yields : ∀ op acc {cs h step j next},
      (body op acc).relation cs h step j next → ∃ result, step = .yield result := by
    intro op acc cs h step j next certificate
    obtain ⟨result,equation,_⟩ := RunnerOperation.operation_index call trace op acc
      ((body op acc).source certificate)
    exact ⟨result,equation⟩
  obtain ⟨op,before,after,j,l,incoming,next,positionEq,prior,bodyCert,suffix,lifted⟩ :=
    list_cut trace.ops.toList (w,#[],#[],#[],#[],#[]) (RunnerOperation.operation call trace)
      body selected yields loop boundList
  have priorRun := (ConservationOuter.forIn (trace.ops.toList.take index)
    (w,#[],#[],#[],#[],#[]) (RunnerOperation.operation call trace) body).source prior
  have atIndex : before.2.1.size = index := by
    have size := RunnerOperationCuts.cut_index call trace trace.ops.toList
      (w,#[],#[],#[],#[],#[]) before (Nat.le_of_lt boundList) priorRun
    simpa only [Array.size_empty,Nat.zero_add] using size
  obtain ⟨returned,received,admitted,front,afterCall⟩ := bodyCert
  refine ⟨op,before,j,incoming,returned.1,returned.2,received,admitted,
    positionEq,atIndex,priorRun,front,?_⟩
  intro inner c selection
  have bodyChosen := operation_selected call rules established queries chosen effects trace op before
    (step := .yield after) (k := l) (final := next)
    ⟨returned,received,admitted,front,afterCall⟩ front selection
  have loopChosen := lifted index inner c (by simpa only [atIndex] using bodyChosen)
  exact RunnerSelectionCuts.bind_left
    (RunnerSelection.loop call rules established queries chosen effects trace (w,#[],#[],#[],#[],#[]))
    (RunnerSelection.finish trace) source loop loopChosen

end Leanux.Proofs.WG.Queues.RxCredits.RunnerOperationSelection
