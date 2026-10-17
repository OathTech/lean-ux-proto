import Leanux.Proofs.WG.Queues.AdmissionSelectionCuts

/-! The literal original entry prefix, before the actual dispatch/tail body.
Its source factor preserves resets and the failing seccomp guard. The run cut
does not assume packet acceptance, a query, or a final ledger. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.SyscallEntryCuts
open Leanux Leanux.WG Leanux.Proofs.Logged

def enter (call : Syscall) : RxHistory.Obs Unit := do
  liftPrefix (modify fun w => {w with fs := {w.fs with userOut := none,userFds := none}, seccomp := {w.seccomp with emitted := {},translatedLen := none}})
  liftPrefix (modifyWG fun g=>{g with queuedThisCall:=[]})
  liftPrefix (modifyAmbient fun a=>{a with steps:=#[],extraOut:=[],fired:=#[],netRxSections:=0,netRxSection:=0})
  match syscallNr call with
  | some nr=>liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none=>
    if call.isNet && (←liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")

def withBody (call : Syscall) (body : RxHistory.Obs α) : RxHistory.Obs α := do
  liftPrefix (modify fun w => {w with fs := {w.fs with userOut := none,userFds := none}, seccomp := {w.seccomp with emitted := {},translatedLen := none}})
  liftPrefix (modifyWG fun g=>{g with queuedThisCall:=[]})
  liftPrefix (modifyAmbient fun a=>{a with steps:=#[],extraOut:=[],fired:=#[],netRxSections:=0,netRxSection:=0})
  match syscallNr call with
  | some nr=>liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none=>
    if call.isNet && (←liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  body

/-- This is precisely the same source prefix, independently of its body. -/
theorem factor (call : Syscall) (body : RxHistory.Obs α) :
    withBody call body=(do enter call;body) := by
  cases choice : syscallNr call
  · simp only [withBody,enter,choice,bind_assoc]
    congr 1
    funext ignored
    congr 1
    funext ignored
    congr 1
    funext ignored
    congr 1
    funext task
    split <;> rfl
  · simp only [withBody,enter,choice,bind_assoc]

/-- A normal source return necessarily passed the actual entry guard and
reached this body. Failing entry has no fabricated body cut. -/
theorem run_cut (call : Syscall) (body : RxHistory.Obs α)
    (run : runPrefix (withBody call body) w h=(.ok (result,v),k)) :
    ∃u j,runPrefix (enter call) w h=(.ok ((),u),j) ∧
      runPrefix body u j=(.ok (result,v),k) := by
  rw [factor,runPrefix_bind] at run
  cases front : runPrefix (enter call) w h with
  | mk outcome j=>
    rw [front] at run
    cases outcome with
    | error reason=>cases run
    | ok out=>
      rcases out with ⟨value,u⟩
      cases value
      exact ⟨u,j,rfl,run⟩

theorem enter_history (call : Syscall) : HistoryFrame some (enter call) := by
  unfold enter
  repeat' first
    | exact HistoryFrame.lift _ _
    | exact HistoryFrame.pure _ _
    | apply HistoryFrame.bind
    | (intro)
    | (split)
    | simp only [runPrefix_lift,runPrefix_pure]

/-- Entry resets native fields, never the incoming proof journal. -/
theorem normal_cut (call : Syscall) (body : RxHistory.Obs α)
    (run : runPrefix (withBody call body) w h=(.ok (result,v),k)) :
    ∃u,runPrefix (enter call) w h=(.ok ((),u),h) ∧
      runPrefix body u h=(.ok (result,v),k) := by
  obtain ⟨u,j,front,tail⟩ := run_cut call body run
  have history := enter_history call w h
  simp only [front,List.filterMap_some] at history
  subst j
  exact ⟨u,front,tail⟩

/-- The existing source-selected entry rule uses this same actual prefix. -/
theorem certificate_cut (call : Syscall) {body : RxHistory.Obs α}
    (checked : ConservationSyscall.Checked loans body)
    (source : (ConservationSyscall.entry call checked).rule.relation cs w h result v k next) :
    ∃u j,runPrefix (enter call) w h=(.ok ((),u),j) ∧
      runPrefix body u j=(.ok (result,v),k) :=
  run_cut call body ((ConservationSyscall.entry call checked).rule.source source)

/-- Only these constructors introduce ingress traffic in dispatch. -/
inductive TrafficCall : Syscall → Prop where
  | inject : TrafficCall (.wgInject family port msg tos ll dest)
  | flood : TrafficCall (.wgFlood count port family messages)
  | batch : TrafficCall (.wgBatch items waitMs)

/-- Traffic entry has no syscall number; the actual current-task read and
seccomp rejection remain ahead of the body. The complete normal certificate
provides that body's source ledger at its unchanged journal. -/
theorem traffic_body (call : Syscall) (traffic : TrafficCall call)
    {body : RxHistory.Obs α} (checked : ConservationSyscall.Checked loans body)
    (source : (ConservationSyscall.entry call checked).rule.relation cs w h result v k next) :
    ∃u,runPrefix (enter call) w h=(.ok ((),u),h) ∧
      checked.rule.relation cs u h result v k next := by
  cases traffic
  all_goals
    dsimp only [ConservationSyscall.entry,syscallNr] at source
    obtain ⟨x,u,j,middle,first,source⟩ := source
    obtain ⟨runOne,rfl,rfl⟩ := first
    obtain ⟨x,u,j,middle,second,source⟩ := source
    obtain ⟨runTwo,rfl,rfl⟩ := second
    obtain ⟨x,u,j,middle,third,source⟩ := source
    obtain ⟨runThree,rfl,rfl⟩ := third
    obtain ⟨task,u,j,middle,current,source⟩ := source
    obtain ⟨readTask,rfl,rfl⟩ := current
    cases guard : task.seccomp.mode != .disabled with
    | false=>
      refine ⟨u,?_,?_⟩
      · unfold enter
        rw [runPrefix_bind,runPrefix_lift,runOne]
        dsimp only
        erw [runPrefix_bind,runPrefix_lift,runTwo]
        dsimp only
        erw [runPrefix_bind,runPrefix_lift,runThree]
        dsimp only [syscallNr]
        erw [runPrefix_bind,runPrefix_lift,readTask]
        simp only [Syscall.isNet,Bool.true_and,guard,Bool.false_eq_true,↓reduceIte,runPrefix_pure]
      · simpa only [ConservationSyscall.Checked.branch,HolderTrafficDispatch.branch,Syscall.isNet,Bool.true_and,guard,Bool.false_eq_true,↓reduceIte] using source
    | true=>
      simp only [ConservationSyscall.Checked.branch,HolderTrafficDispatch.branch,Syscall.isNet,Bool.true_and,guard] at source
      obtain ⟨impossible,_,_⟩ := source
      cases impossible

/-- Any admission chosen at the actual body cut lifts through entry. The
selection premise sees the source prefix, not a final ledger membership. -/
theorem traffic_selected (call : Syscall) (traffic : TrafficCall call)
    {body : RxHistory.Obs α} (checked : ConservationSyscall.Checked loans body)
    (query : AdmissionSelection.Query checked.rule)
    (source : (ConservationSyscall.entry call checked).rule.relation cs w h result v k next)
    (chosen : ∀u,runPrefix (enter call) w h=(.ok ((),u),h)→
      ∀certificate : checked.rule.relation cs u h result v k next,query certificate c) :
    SyscallSelection.entry call checked query source c := by
  cases traffic
  all_goals
    dsimp only [ConservationSyscall.entry,syscallNr] at source
    dsimp only [SyscallSelection.entry]
    obtain ⟨x,u,j,middle,first,source⟩ := source
    refine ⟨x,u,j,middle,first,source,?_⟩
    obtain ⟨runOne,rfl,rfl⟩ := first
    obtain ⟨x,u,j,middle,second,source⟩ := source
    refine ⟨x,u,j,middle,second,source,?_⟩
    obtain ⟨runTwo,rfl,rfl⟩ := second
    obtain ⟨x,u,j,middle,third,source⟩ := source
    refine ⟨x,u,j,middle,third,source,?_⟩
    obtain ⟨runThree,rfl,rfl⟩ := third
    obtain ⟨task,u,j,middle,current,source⟩ := source
    refine ⟨task,u,j,middle,current,source,?_⟩
    obtain ⟨readTask,rfl,rfl⟩ := current
    dsimp only at source
    revert source
    simp only [Syscall.isNet,Bool.true_and]
    generalize guard : (task.seccomp.mode != .disabled) = flag
    intro source
    cases flag with
    | false=>
      simp only [AdmissionSelection.branch]
      apply chosen u
      · unfold enter
        rw [runPrefix_bind,runPrefix_lift,runOne]
        dsimp only
        erw [runPrefix_bind,runPrefix_lift,runTwo]
        dsimp only
        erw [runPrefix_bind,runPrefix_lift,runThree]
        dsimp only [syscallNr]
        erw [runPrefix_bind,runPrefix_lift,readTask]
        simp only [Syscall.isNet,Bool.true_and,guard,Bool.false_eq_true,↓reduceIte,runPrefix_pure]
    | true=>
      simp only [ConservationSyscall.Checked.branch,HolderTrafficDispatch.branch,Bool.true_and] at source
      obtain ⟨impossible,_,_⟩ := source
      cases impossible

/-- An independently supplied normal entry cut selects the same body
certificate by determinism, including the exact incoming history. -/
theorem traffic_selected_at (call : Syscall) (traffic : TrafficCall call)
    {body : RxHistory.Obs α} (checked : ConservationSyscall.Checked loans body)
    (query : AdmissionSelection.Query checked.rule)
    (source : (ConservationSyscall.entry call checked).rule.relation cs w h result v k next)
    (front : runPrefix (enter call) w h=(.ok ((),u),h))
    (bodySource : checked.rule.relation cs u h result v k next)
    (selected : query bodySource c) :
    SyscallSelection.entry call checked query source c := by
  apply traffic_selected call traffic checked query source
  intro actual entered certificate
  obtain ⟨⟨_,rfl⟩,_⟩ := entered.symm.trans front
  exact selected

/-- The original syscall source equality changes only its type index. -/
theorem mpr_selected {action other : RxHistory.Obs α}
    (same : action=other)
    (types : ConservationSyscall.Checked loans action=ConservationSyscall.Checked loans other)
    (checked : ConservationSyscall.Checked loans other)
    (query : AdmissionSelection.Query checked.rule)
    (source : (Eq.mpr types checked).rule.relation cs w h result v k next)
    (selected : ∀certificate : checked.rule.relation cs w h result v k next,query certificate c) :
    SyscallSelection.mpr same types checked query source c := by
  cases same
  exact selected source

end Leanux.Proofs.WG.Queues.RxCredits.SyscallEntryCuts
