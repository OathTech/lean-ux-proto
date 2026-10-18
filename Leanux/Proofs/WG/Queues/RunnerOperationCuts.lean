import Leanux.Proofs.WG.Queues.RunnerOperation

/-! Independent source cuts for every position of the original normal runner
loop. These theorems use only the actual action equations: no admission query,
carrier ledger, or final funding assertion is an input. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerOperationCuts
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open RunnerOperation

theorem cons_normal {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace)
    (op : Operation) (ops : List Operation) (state : State) {h k : List E} {out : State}
    (run : runPrefixOuter (forIn (op::ops) state (operation call trace)) h = (.ok out,k)) :
    ∃ middle j,
      runPrefixOuter (operation call trace op state) h = (.ok (.yield middle),j) ∧
      runPrefixOuter (forIn ops middle (operation call trace)) j = (.ok out,k) := by
  rw [List.forIn_cons] at run
  obtain ⟨step,j,front,rest⟩ := bind_normal run
  obtain ⟨middle,rfl,_⟩ := operation_index call trace op state front
  exact ⟨middle,j,front,rest⟩

theorem list_index {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace)
    (ops : List Operation) (state : State) {h k : List E} {out : State}
    (run : runPrefixOuter (forIn ops state (operation call trace)) h = (.ok out,k)) :
    out.2.1.size = state.2.1.size + ops.length := by
  induction ops generalizing state h with
  | nil =>
    simp only [List.forIn_nil,runPrefixOuter_pure,Prod.mk.injEq,Except.ok.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact (Nat.add_zero _).symm
  | cons op ops ih =>
    obtain ⟨middle,j,front,rest⟩ := cons_normal call trace op ops state run
    obtain ⟨same,eq,size⟩ := operation_index call trace op state front
    cases eq
    rw [ih middle rest,size]
    simp only [List.length_cons,Nat.add_assoc,Nat.add_comm 1]

/-- The prefix and suffix are literal take/drop portions of the original
loop. Equal operation values cannot change the selected numeric position. -/
theorem list_cut {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace)
    (ops : List Operation) (state : State) {h k : List E} {out : State} {index : Nat}
    (run : runPrefixOuter (forIn ops state (operation call trace)) h = (.ok out,k))
    (bound : index < ops.length) :
    ∃ op before after j l,
      ops[index]? = some op ∧
      runPrefixOuter (forIn (ops.take index) state (operation call trace)) h = (.ok before,j) ∧
      runPrefixOuter (operation call trace op before) j = (.ok (.yield after),l) ∧
      runPrefixOuter (forIn (ops.drop (index+1)) after (operation call trace)) l = (.ok out,k) := by
  induction ops generalizing state h index with
  | nil => simp at bound
  | cons op ops ih =>
    obtain ⟨middle,j,front,rest⟩ := cons_normal call trace op ops state run
    cases index with
    | zero => exact ⟨op,state,middle,h,j,rfl,rfl,front,rest⟩
    | succ index =>
      obtain ⟨selected,before,after,l,m,positionEq,priorRun,body,suffix⟩ :=
        ih middle rest (Nat.lt_of_succ_lt_succ bound)
      refine ⟨selected,before,after,l,m,positionEq,?_,body,suffix⟩
      simp only [List.take_succ_cons,List.forIn_cons,runPrefixOuter_bind,front]
      exact priorRun

theorem cut_index {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace)
    (ops : List Operation) (state before : State) {h j : List E} {index : Nat}
    (bound : index ≤ ops.length)
    (priorRun : runPrefixOuter (forIn (ops.take index) state (operation call trace)) h = (.ok before,j)) :
    before.2.1.size = state.2.1.size + index := by
  have size := list_index call trace (ops.take index) state priorRun
  simpa only [List.length_take,Nat.min_eq_left bound] using size

/-- Every bounded operation position of an actual normal runner tail has
its original syscall cut. The source-selected accumulator supplies `ends`
and `results`; the invocation uses this exact operation number. -/
theorem tail_cut {E α : Type} (call : Syscall → PrefixM E Int)
    (finish : Json → World → α) (trace : Trace) (w : World)
    {h k : List E} {result : α} {index : Nat}
    (run : runPrefixOuter (RoutingJoint.runnerTailWith call finish trace w) h = (.ok result,k))
    (bound : index < trace.ops.size) :
    ∃ op before after complete j l done ret returned received,
      trace.ops.toList[index]? = some op ∧ before.2.1.size = index ∧
      runPrefixOuter (forIn (trace.ops.toList.take index) (w,#[],#[],#[],#[],#[])
        (operation call trace)) h = (.ok before,j) ∧
      runPrefix (call (toSyscall before.2.1 before.2.2.1 index op))
        (prepare trace before) j = (.ok (ret,returned),received) ∧
      runPrefixOuter (afterCall op before ret returned) received = (.ok (.yield after),l) ∧
      runPrefixOuter (forIn (trace.ops.toList.drop (index+1)) after
        (operation call trace)) l = (.ok complete,done) ∧
      runPrefixOuter (finishWith finish trace complete) done = (.ok result,k) := by
  rw [tail_factor] at run
  obtain ⟨complete,done,loop,finishRun⟩ := bind_normal run
  rw [← Array.forIn_toList] at loop
  have boundList : index < trace.ops.toList.length := by simpa using bound
  obtain ⟨op,before,after,j,l,positionEq,priorRun,body,suffix⟩ :=
    list_cut call trace trace.ops.toList (w,#[],#[],#[],#[],#[]) loop boundList
  have atIndex : before.2.1.size = index := by
    have size := cut_index call trace trace.ops.toList (w,#[],#[],#[],#[],#[]) before
      (Nat.le_of_lt boundList) priorRun
    simpa only [Array.size_empty,Nat.zero_add] using size
  obtain ⟨ret,returned,received,syscallRun,afterRun⟩ := operation_cut call trace op before body
  exact ⟨op,before,after,complete,j,l,done,ret,returned,received,positionEq,atIndex,priorRun,
    by simpa only [atIndex] using syscallRun,afterRun,suffix,finishRun⟩

end Leanux.Proofs.WG.Queues.RxCredits.RunnerOperationCuts
