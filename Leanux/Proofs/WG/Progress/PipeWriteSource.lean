import Leanux.Proofs.WG.Progress.PipeWriteFrames
import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Init.Internal.Order.While

/-! Exact finite evaluator for pipeWriteToOut. Every reachable yield decreases
remaining copy count; the full-buffer arm retains its original stopping path.
The evaluator uses the concrete finite allocation encounter, including Stops. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PipeWrite
open Leanux PipeFree
def CopyEffect (src : IovIter) (requested : Nat) (out : Nat × IovIter) : Prop :=
  out.1 ≤ min requested src.count ∧ out.2.bytes=src.bytes ∧
  out.2.pos=src.pos+out.1 ∧ out.2.count=src.count-out.1


theorem copy_effect (page : PageId) (offset requested : Nat) (src : IovIter)
    (f g : FSWorld) (t u : TaskWorld) (a b : Ambient) (out : Nat × IovIter)
    (hr : run (copyPageFromIter page offset requested src) f t a = .ok (((out,g),u),b)) :
    CopyEffect src requested out := by
  cases he : (AmbientM.envOk .copyPageFromIter).run a with
  | error e => simp [copyPageFromIter,he] at hr
  | ok pair =>
    obtain ⟨ok,a'⟩:=pair
    cases ok
    · simp [copyPageFromIter,he] at hr
      rcases hr with ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
      simp [CopyEffect]
    · simp [copyPageFromIter,he,getPage] at hr
      cases pg : f.pages[page]? with
      | none => simp [pg] at hr
      | some p =>
        by_cases bound : offset+min requested src.count>p.bytes.size
        · simp [pg,bound] at hr
        · simp [pg,bound,setPage] at hr
          rcases hr with ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
          refine ⟨Nat.le_refl _,rfl,rfl,?_⟩
          simp only [IovIter.count]
          omega

theorem copy_decreases (src : IovIter) (out : Nat × IovIter)
    (effect : CopyEffect src PAGE_SIZE out)
    (notShort : ¬ out.1 < PAGE_SIZE) :
    out.2.count < src.count := by
  have pagePositive : 0 < PAGE_SIZE := by decide
  obtain ⟨bound,_,_,count⟩:=effect
  omega


def blocked (iocb : Kiocb) (filp : File) (state : IovIter × Int) :
    FS.M (ForInStep (IovIter × Int)) := do
  let src := state.1
  let mut ret := state.2
  let nonblock ← do
    if ← branchCmp .pipeWriteNonblock (hasFlag filp.fFlags O_NONBLOCK)
        (filp.fFlags &&& O_NONBLOCK).toNat 0 then pure true
    else branchCmp .pipeWriteNowait (hasFlag iocb.kiFlags IOCB_NOWAIT) (iocb.kiFlags &&& IOCB_NOWAIT).toNat 0
  if nonblock then
    if ← branchCmp .pipeWriteNoRet (ret == 0) ret 0 then ret := -EAGAIN
    return .done (src,ret)
  unsupported "pipe_write: blocking wait (signal_pending, wait_event_interruptible_exclusive)"
  return .yield (src,ret)


def after (iocb : Kiocb) (filp : File) (pid : PipeId) (head : UInt32)
    (state : IovIter × Int) : FS.M (ForInStep (IovIter × Int)) := do
  let p ← getPipe pid
  if ← branch .pipeWriteStaleNotFull (!pipeFull head p.tail p.maxUsage) then
    return .yield state
  blocked iocb filp state

def fillWith (alloc : FS.M Bool) (iocb : Kiocb) (filp : File) (pid : PipeId)
    (p : PipeInodeInfo) (state : IovIter × Int) : FS.M (ForInStep (IovIter × Int)) := do
  let mut src := state.1
  let mut ret := state.2
  let head := p.head
  let mut page := p.tmpPage
  if ← branch .pipeWriteNoTmpPage page.isNone then
    if ← branch .pipeWriteAllocFailed !(← alloc) then
      if !(← branchCmp .pipeWriteAllocRet (ret != 0) ret 0) then ret := -ENOMEM
      return .done (src,ret)
    let pg ← newPipePage
    page := some pg
    setPipe pid { (← getPipe pid) with tmpPage := some pg }
  let some pg := page | invariant "unreachable"
  setPipe pid { (← getPipe pid) with head := head + 1 }
  let i ← pipeBufIdx (← getPipe pid) head
  let flags := if ← branchCmp .pipeWritePacketized (hasFlag filp.fFlags O_DIRECT)
      (filp.fFlags &&& O_DIRECT).toNat 0 then PIPE_BUF_FLAG_PACKET else PIPE_BUF_FLAG_CAN_MERGE
  setPipeBuf pid i { page := some pg, ops := true, offset := 0, len := 0, flags }
  setPipe pid { (← getPipe pid) with tmpPage := none }
  let (copied, src') ← copyPageFromIter pg 0 PAGE_SIZE src
  src := src'
  let fault ← do
    if ← branchCmp .pipeWriteShortCopy (copied < PAGE_SIZE) copied PAGE_SIZE then
      branchCmp .pipeWriteShortCopyLeft (src.count != 0) src.count 0
    else pure false
  if fault then
    if ← branchCmp .pipeWriteFaultNoRet (ret == 0) ret 0 then ret := -EFAULT
    return .done (src,ret)
  ret := ret + copied
  setPipeBuf pid i { (← getPipeBuf pid i) with len := copied }
  if ← branchCmp .pipeWriteDone (src.count == 0) src.count 0 then return .done (src,ret)
  after iocb filp pid head (src,ret)

def stepWith (alloc : FS.M Bool) (iocb : Kiocb) (filp : File) (pid : PipeId)
    (state : IovIter × Int) : FS.M (ForInStep (IovIter × Int)) := do
  let src := state.1
  let mut ret := state.2
  let p ← getPipe pid
  if ← branch .pipeWriteLoopNoReaders (p.readers == 0) then
    _ ← sendSig .task SIGPIPE 0
    if ← branchCmp .pipeWriteLoopNoRet (ret == 0) ret 0 then ret := -EPIPE
    return .done (src,ret)
  if ← branchCmp .pipeWriteNotFull (!pipeFull p.head p.tail p.maxUsage)
      (pipeOccupancy p.head p.tail) p.maxUsage then
    fillWith alloc iocb filp pid p (src,ret)
  else after iocb filp pid p.head (src,ret)

def step (iocb : Kiocb) (filp : File) (pid : PipeId) :=
  stepWith (hiddenAlloc .allocPipePage) iocb filp pid

def loop (iocb : Kiocb) (filp : File) (pid : PipeId) (s : IovIter × Int) : FS.M (IovIter × Int) :=
  Lean.Loop.forIn Lean.Loop.mk s (fun _ s=>step iocb filp pid s)

def withLoop (iterate : IovIter × Int → FS.M (IovIter × Int))
    (pid : PipeId) (src : IovIter) : FS.M (Int × Bool) := do
  let totalLen := src.count
  let mut src := src
  let p ← getPipe pid
  if ← branchCmp .pipeWriteNoReaders (p.readers == 0) p.readers 0 then
    _ ← sendSig .task SIGPIPE 0
    return (-EPIPE, false)
  let head := p.head
  let wasEmpty := head == p.tail
  let chars := totalLen % PAGE_SIZE
  let mut ret : Int := 0
  let merge ← do
    if ← branchCmp .pipeWriteChars (chars != 0) chars 0 then branch .pipeWriteNotWasEmpty !wasEmpty
    else pure false
  if merge then
    let i ← pipeBufIdx p (head - 1)
    let buf ← getPipeBuf pid i
    let offset := buf.offset + buf.len
    let fits ← do
      if ← branchCmp .pipeWriteCanMerge (hasFlag buf.flags PIPE_BUF_FLAG_CAN_MERGE)
          (buf.flags &&& PIPE_BUF_FLAG_CAN_MERGE).toNat 0 then
        branchCmp .pipeWriteFits (offset + chars <= PAGE_SIZE) (offset + chars) PAGE_SIZE
      else pure false
    if fits then
      ret ← pipeBufConfirm buf
      if ← branch .pipeWriteMergeConfirmErr (ret != 0) then return (ret, wasEmpty)
      let some page := buf.page | invariant "pipe_write: a buffer with a NULL page"
      let (n, src') ← copyPageFromIter page offset chars src
      src := src'
      ret := n
      if ← branchCmp .pipeWriteMergeShort (ret < chars) ret chars then return (-EFAULT, wasEmpty)
      setPipeBuf pid i { (← getPipeBuf pid i) with len := buf.len + n }
      if ← branchCmp .pipeWriteMergeDone (src.count == 0) src.count 0 then return (ret, wasEmpty)
  let out ← iterate (src,ret)
  return (out.2,wasEmpty)

theorem original_source (iocb : Kiocb) (filp : File) (pid : PipeId) (src : IovIter) :
    pipeWriteToOut iocb filp pid src =
      withLoop (loop iocb filp pid) pid src := rfl


def Result {α : Type} (action : FS.M α) (Q : α → Prop) : Prop :=
  ∀ f t a x g u b, run action f t a = .ok (((x,g),u),b) → Q x

theorem result_bind {α β : Type} (action : FS.M α) (next : α → FS.M β) (Q : β → Prop)
    (each : ∀ x, Result (next x) Q) : Result (action >>= next) Q := by
  intro f t a y g u b hr
  rw [run_bind] at hr
  cases he : run action f t a with
  | error e => simp [he] at hr
  | ok out =>
    rcases out with ⟨⟨⟨x,v⟩,w⟩,c⟩
    simp only [he,ok_bind] at hr
    exact each x v w c y g u b hr

theorem result_branch {α : Type} (d : Decision) (v : Bool) (next : Bool → FS.M α)
    (Q : α → Prop) (each : Result (next v) Q) :
    Result (do let x←branch d v; next x) Q := by
  intro f t a x g u b hr
  simp only [run_bind,run_branch,ok_bind] at hr
  exact each _ _ _ _ _ _ _ hr

theorem result_cmp {α : Type} (d : Decision) (v : Bool) (n m : Int)
    (next : Bool → FS.M α) (Q : α → Prop) (each : Result (next v) Q) :
    Result (do let x←branchCmp d v n m; next x) Q := by
  intro f t a x g u b hr
  simp only [run_bind,run_cmp,ok_bind] at hr
  exact each _ _ _ _ _ _ _ hr

theorem result_copy {α : Type} (pg : PageId) (offset requested : Nat) (src : IovIter)
    (next : Nat × IovIter → FS.M α) (Q : α → Prop)
    (each : ∀out, CopyEffect src requested out → Result (next out) Q) :
    Result (do let out←copyPageFromIter pg offset requested src; next out) Q := by
  intro f t a x g u b hr
  rw [run_bind] at hr
  cases he : run (copyPageFromIter pg offset requested src) f t a with
  | error e => simp [he] at hr
  | ok out =>
    rcases out with ⟨⟨⟨out,v⟩,w⟩,c⟩
    simp only [he,ok_bind] at hr
    exact each out (copy_effect pg offset requested src f v t w a c out he) v w c x g u b hr

theorem result_stop {α : Type} (s : String) (Q : α → Prop) :
    Result (invariant s) Q := by
  intro f t a x g u b hr
  cases hr

theorem result_unsupported {α : Type} (s : String) (Q : α → Prop) :
    Result (unsupported s) Q := by
  intro f t a x g u b hr
  cases hr

theorem result_pure {α : Type} (x : α) (Q : α → Prop) (h : Q x) :
    Result (pure x) Q := by
  intro f t a y g u b hr
  cases hr
  exact h

def Progress (src : IovIter) (out : ForInStep (IovIter × Int)) : Prop :=
  match out with
  | .done _ => True
  | .yield next => next.1.count < src.count


theorem after_progress (iocb : Kiocb) (filp : File) (pid : PipeId) (head : UInt32)
    (initial : IovIter) (state : IovIter × Int) (smaller : state.1.count<initial.count) :
    Result (after iocb filp pid head state) (Progress initial) := by
  unfold after blocked
  repeat' first
    | with_reducible apply result_branch
    | with_reducible apply result_cmp
    | with_reducible exact result_stop _ _
    | with_reducible exact result_unsupported _ _
    | (with_reducible apply result_pure; simp only [Progress]; try exact smaller)
    | with_reducible apply result_bind
    | split
    | (with_reducible intro x; try dsimp only)
    | (dsimp only; split)

theorem count_contradiction (n : Nat) (h : ¬ (n != 0) = true) (h' : ¬ (n == 0) = true) : False := by
  simp_all

theorem fill_progress (alloc : FS.M Bool) (iocb : Kiocb) (filp : File) (pid : PipeId)
    (p : PipeInodeInfo) (state : IovIter × Int) :
    Result (fillWith alloc iocb filp pid p state) (Progress state.1) := by
  unfold fillWith
  repeat' first
    | solve | exfalso; apply count_contradiction; assumption; assumption
    | with_reducible apply result_copy
    | with_reducible apply result_branch
    | with_reducible apply result_cmp
    | with_reducible exact result_stop _ _
    | with_reducible exact result_unsupported _ _
    | (with_reducible apply result_pure; simp only [Progress])
    | (with_reducible apply after_progress; apply copy_decreases; assumption; simpa only [Bool.not_eq_true, decide_eq_false_iff_not] using (by assumption : ¬ decide (_ < PAGE_SIZE) = true))
    | with_reducible apply result_bind
    | split
    | (with_reducible intro x; try dsimp only)
    | (dsimp only; split)


theorem after_factor (iocb : Kiocb) (filp : File) (pid : PipeId) (head : UInt32)
    (state : IovIter × Int) :
    after iocb filp pid head state = (do
      let p ← getPipe pid
      if ← branch .pipeWriteStaleNotFull (!pipeFull head p.tail p.maxUsage) then
        pure (.yield state)
      else blocked iocb filp state) := rfl

theorem result_unsupported_bind {α β : Type} (s : String) (next : α → FS.M β) (Q : β → Prop) :
    Result (unsupported s >>= next) Q := by
  intro f t a x g u b hr
  cases hr

theorem blocked_progress (iocb : Kiocb) (filp : File) (state : IovIter × Int) (initial : IovIter) :
    Result (blocked iocb filp state) (Progress initial) := by
  unfold blocked
  repeat' first
    | with_reducible exact result_unsupported_bind _ _ _
    | with_reducible apply result_branch
    | with_reducible apply result_cmp
    | with_reducible exact result_stop _ _
    | with_reducible exact result_unsupported _ _
    | (with_reducible apply result_pure; simp only [Progress])
    | with_reducible apply result_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem step_progress (alloc : FS.M Bool) (iocb : Kiocb) (filp : File) (pid : PipeId)
    (state : IovIter × Int) :
    Result (stepWith alloc iocb filp pid state) (Progress state.1) := by
  intro f t a x g u b hr
  cases hp : f.pipes[pid]? with
  | none => simp [stepWith,getPipe,hp] at hr
  | some p =>
    by_cases readers : p.readers=0
    · have done : Result (do
          let _ ← sendSig .task SIGPIPE 0
          let ret ← if ← branchCmp .pipeWriteLoopNoRet (state.2 == 0) state.2 0
            then pure (-EPIPE) else pure state.2
          pure (.done (state.1,ret))) (Progress state.1) := by
        repeat' first
          | with_reducible apply result_cmp
          | (with_reducible apply result_pure; simp only [Progress])
          | with_reducible apply result_bind
          | split
          | (with_reducible intro y; try dsimp only)
      simp [stepWith,getPipe,hp,readers] at hr
      apply done f t {a with steps:=a.steps.push {decision:=.pipeWriteLoopNoReaders,outcome:=true,netRx:=a.netRxSection}} x g u b
      simpa [run_bind,run_cmp] using hr
    · by_cases full : pipeFull p.head p.tail p.maxUsage=true
      · simp [stepWith,getPipe,hp,readers,full,after_factor] at hr
        exact blocked_progress iocb filp state state.1 _ _ _ _ _ _ _ hr
      · simp [stepWith,getPipe,hp,readers,full] at hr
        exact fill_progress alloc iocb filp pid p state _ _ _ _ _ _ _ hr

def finiteStep (iocb : Kiocb) (filp : File) (pid : PipeId) :=
  stepWith (monadLift (hiddenAllocFinite .allocPipePage)) iocb filp pid

def evaluate (iocb : Kiocb) (filp : File) (pid : PipeId) :
    Nat → IovIter × Int → FS.M (IovIter × Int)
  | 0, _ => invariant "proof-side pipe-write fuel exhausted"
  | fuel+1,state => do
    match ← finiteStep iocb filp pid state with
    | .done next => pure next
    | .yield next => evaluate iocb filp pid fuel next

def finite (iocb : Kiocb) (filp : File) (pid : PipeId) (src : IovIter) : FS.M (Int × Bool) :=
  withLoop (fun s=>evaluate iocb filp pid (s.1.count+1) s) pid src

theorem step_finite (iocb : Kiocb) (filp : File) (pid : PipeId) :
    step iocb filp pid = finiteStep iocb filp pid := by
  unfold step finiteStep hiddenAlloc
  rw [hiddenAlloc_finite_source]

theorem loop_unfold (iocb : Kiocb) (filp : File) (pid : PipeId) (state : IovIter × Int) :
    loop iocb filp pid state = (do
      match ← step iocb filp pid state with
      | .done next => pure next
      | .yield next => loop iocb filp pid next) := by
  unfold loop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  apply bind_congr
  intro out
  cases out <;> rfl

theorem loop_finite (iocb : Kiocb) (filp : File) (pid : PipeId)
    (fuel : Nat) (state : IovIter × Int) (f : FSWorld) (t : TaskWorld) (a : Ambient)
    (enough : state.1.count<fuel) :
    run (loop iocb filp pid state) f t a =
      run (evaluate iocb filp pid fuel state) f t a := by
  induction fuel generalizing state f t a with
  | zero => omega
  | succ fuel ih =>
    rw [loop_unfold,step_finite,evaluate]
    simp only [run_bind]
    cases he : run (finiteStep iocb filp pid state) f t a with
    | error e => rfl
    | ok v =>
      rcases v with ⟨⟨⟨out,g⟩,u⟩,b⟩
      simp only [ok_bind]
      cases out with
      | done next => rfl
      | yield next =>
        have smaller := step_progress (monadLift (hiddenAllocFinite .allocPipePage))
          iocb filp pid state f t a (.yield next) g u b he
        apply ih
        change next.1.count<state.1.count at smaller
        omega

theorem finite_source (iocb : Kiocb) (filp : File) (pid : PipeId) (src : IovIter) :
    pipeWriteToOut iocb filp pid src = finite iocb filp pid src := by
  rw [original_source]
  unfold finite
  congr 1
  funext state f t a
  exact loop_finite iocb filp pid (state.1.count+1) state f t a (by omega)

end Leanux.Proofs.WG.Progress.PipeWrite
