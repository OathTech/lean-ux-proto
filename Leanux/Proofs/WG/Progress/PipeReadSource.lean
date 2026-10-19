import Leanux.Proofs.WG.Progress.PipeReadFrames
import Init.Internal.Order.While

/-! Exact whole pipeRead finite evaluation. Remaining length plus modular
occupancy strictly decreases on every actual yielded iteration. All reads,
copies, releases, wake callbacks, timestamps and original Stops are retained. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PipeRead
open Leanux PipeFree


def blocked (iocb : Kiocb) (filp : File) (pid : PipeId) (state : Nat × Int) :
    FS.M (ForInStep (Nat × Int)) := do
  let p ← getPipe pid
  if ← branchCmp .pipeReadNoWriters (p.writers == 0) p.writers 0 then return .done state
  if ← branchCmp .pipeReadHaveData (state.2 != 0) state.2 0 then return .done state
  let nonblock ← do
    if ← branchCmp .pipeReadNonblock (hasFlag filp.fFlags O_NONBLOCK)
        (filp.fFlags &&& O_NONBLOCK).toNat 0 then pure true
    else branchCmp .pipeReadNowait (hasFlag iocb.kiFlags IOCB_NOWAIT) (iocb.kiFlags &&& IOCB_NOWAIT).toNat 0
  if nonblock then return .done (state.1,-EAGAIN)
  unsupported "pipe_read: blocking wait (wait_event_interruptible_exclusive)"
  return .yield state

def finishItem (iocb : Kiocb) (filp : File) (pid : PipeId)
    (head tail : UInt32) (i totalLen : Nat) (ret : Int) (buf : PipeBuffer) (chars : Nat) :
    FS.M (ForInStep (Nat × Int)) := do
  let mut tail := tail
  setPipeBuf pid i buf
  if ← branch .pipeReadBufEmpty (buf.len == 0) then
    tail ← pipeUpdateTail pid i tail
  let totalLen := totalLen - chars
  if ← branch .pipeReadDone (totalLen == 0) then return .done (totalLen,ret)
  if ← branchCmp .pipeReadMore (head != tail) head.toNat tail.toNat then
    return .yield (totalLen,ret)
  blocked iocb filp pid (totalLen,ret)

def copyItem (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat)
    (head tail : UInt32) (i : Nat) (state : Nat × Int) (buf : PipeBuffer) (chars : Nat) :
    FS.M (ForInStep (Nat × Int)) := do
  let mut totalLen := state.1
  let mut ret := state.2
  let error ← pipeBufConfirm buf
  if ← branch .pipeReadConfirmError (error != 0) then
    unsupported "pipe_read: pipe_buf_confirm failed"
  let some page := buf.page | invariant "pipe_read: a buffer with a NULL page"
  let written ← copyPageToIter page buf.offset chars count
  if ← branchCmp .pipeReadShortCopy (written < chars) written chars then
    if ← branchCmp .pipeReadFaultNoRet (ret == 0) ret 0 then ret := -EFAULT
    return .done (totalLen,ret)
  ret := ret + chars
  let mut buf := {buf with offset:=buf.offset+chars,len:=buf.len-chars}
  if ← branchCmp .pipeReadPacket (hasFlag buf.flags PIPE_BUF_FLAG_PACKET)
      (buf.flags &&& PIPE_BUF_FLAG_PACKET).toNat 0 then
    totalLen := chars
    buf := {buf with len:=0}
  finishItem iocb filp pid head tail i totalLen ret buf chars

def step (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat) (state : Nat × Int) :
    FS.M (ForInStep (Nat × Int)) := do
  let p ← getPipe pid
  if ← branchCmp .pipeReadNotEmpty (p.head != p.tail) p.head.toNat p.tail.toNat then
    let i ← pipeBufIdx p p.tail
    let buf ← getPipeBuf pid i
    let mut chars := buf.len
    if ← branchCmp .pipeReadCharsOver (chars > state.1) chars state.1 then
      if ← branchCmp .pipeReadWhole (hasFlag buf.flags PIPE_BUF_FLAG_WHOLE)
          (buf.flags &&& PIPE_BUF_FLAG_WHOLE).toNat 0 then
        unsupported "pipe_read: PIPE_BUF_FLAG_WHOLE (a notification buffer)"
      chars := state.1
    copyItem iocb filp pid count p.head p.tail i state buf chars
  else blocked iocb filp pid state

def loop (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat) (state : Nat × Int) :
    FS.M (Nat × Int) :=
  Lean.Loop.forIn Lean.Loop.mk state (fun _ s=>step iocb filp pid count s)

def withLoop (iterate : File → PipeId → Nat × Int → FS.M (Nat × Int))
    (iocb : Kiocb) (count : Nat) : FS.M Int := do
  let filp ← getFile iocb.filp
  let pid ← pipeOf filp
  if ← branchCmp .pipeReadNull (count == 0) count 0 then return 0
  modify fun w => {w with userOut:=some ByteArray.empty}
  let p0 ← getPipe pid
  let wasFull := pipeFull p0.head p0.tail p0.maxUsage
  let mut wakeNextReader := false
  let out ← iterate filp pid (count,0)
  let ret := out.2
  let p ← getPipe pid
  if ← branchCmp .pipeReadEmptyAtEnd (p.head == p.tail) p.head.toNat p.tail.toNat then
    wakeNextReader := false
  if ← branch .pipeReadWasFull wasFull then
    wakeUpInterruptibleSyncPoll (.pipeWr pid) (EPOLLOUT ||| EPOLLWRNORM)
  if ← branch .pipeReadWakeNextReader wakeNextReader then
    wakeUpInterruptibleSyncPoll (.pipeRd pid) (EPOLLIN ||| EPOLLRDNORM)
  killFasync p.fasyncWriters
  if ← branchCmp .pipeReadPositive (ret > 0) ret 0 then fileAccessed (← getFile iocb.filp)
  return ret

theorem original_source (iocb : Kiocb) (count : Nat) :
    pipeRead iocb count = withLoop (fun f p=>loop iocb f p count) iocb count := rfl

theorem occupancy_step (head tail : UInt32) (ne : head ≠ tail) :
    pipeOccupancy head (tail+1) < pipeOccupancy head tail := by
  simp only [pipeOccupancy,UInt32.toNat_sub,UInt32.toNat_add,UInt32.reduceToNat]
  have hh:=head.toNat_lt
  have ht:=tail.toNat_lt
  have diff:head.toNat≠tail.toNat:=fun h=>ne (UInt32.toNat_inj.mp h)
  omega

def Spec {α : Type} (pid : PipeId) (head tail : UInt32) (action : FS.M α)
    (Q : α → FSWorld → Prop) : Prop :=
  ∀ f t a x g u b, ends pid f=some (head,tail) →
    run action f t a=.ok (((x,g),u),b) → Q x g

theorem framed_bind {α β : Type} (pid : PipeId) (head tail : UInt32)
    (action : FS.M α) (next : α → FS.M β) (Q : β → FSWorld → Prop)
    (frame : Frame pid action) (each : ∀x,Spec pid head tail (next x) Q) :
    Spec pid head tail (action >>= next) Q := by
  intro f t a y g u b before hr
  rw [run_bind] at hr
  cases he : run action f t a with
  | error e => simp [he] at hr
  | ok pair =>
    rcases pair with ⟨⟨⟨x,m⟩,v⟩,c⟩
    simp only [he,ok_bind] at hr
    exact each x m v c y g u b ((frame f t a x m v c he).trans before) hr

theorem spec_branch {α : Type} (pid : PipeId) (head tail : UInt32)
    (d : Decision) (v : Bool) (next : Bool → FS.M α) (Q : α → FSWorld → Prop)
    (each : Spec pid head tail (next v) Q) :
    Spec pid head tail (do let x←branch d v; next x) Q := by
  intro f t a x g u b before hr
  simp only [run_bind,run_branch,ok_bind] at hr
  exact each _ _ _ _ _ _ _ before hr

theorem spec_cmp {α : Type} (pid : PipeId) (head tail : UInt32)
    (d : Decision) (v : Bool) (n m : Int) (next : Bool → FS.M α) (Q : α → FSWorld → Prop)
    (each : Spec pid head tail (next v) Q) :
    Spec pid head tail (do let x←branchCmp d v n m; next x) Q := by
  intro f t a x g u b before hr
  simp only [run_bind,run_cmp,ok_bind] at hr
  exact each _ _ _ _ _ _ _ before hr

theorem spec_pure {α : Type} (pid : PipeId) (head tail : UInt32)
    (x : α) (Q : α → FSWorld → Prop)
    (each : ∀f,ends pid f=some (head,tail)→Q x f) :
    Spec pid head tail (pure x) Q := by
  intro f t a y g u b before hr
  cases hr
  exact each f before

theorem spec_pure_bind {α β : Type} (pid : PipeId) (head tail : UInt32)
    (x : α) (next : α → FS.M β) (Q : β → FSWorld → Prop)
    (each : Spec pid head tail (next x) Q) :
    Spec pid head tail (pure x >>= next) Q := by
  simpa only [pure_bind] using each

theorem spec_bad_bind {α β : Type} (pid : PipeId) (head tail : UInt32)
    (s : String) (next : α → FS.M β) (Q : β → FSWorld → Prop) :
    Spec pid head tail (unsupported s >>= next) Q := by
  intro f t a x g u b before hr
  cases hr

theorem spec_invariant {α : Type} (pid : PipeId) (head tail : UInt32)
    (s : String) (Q : α → FSWorld → Prop) :
    Spec pid head tail (invariant s) Q := by
  intro f t a x g u b before hr
  cases hr

theorem spec_read {α : Type} (pid : PipeId) (head tail : UInt32)
    (next : PipeInodeInfo → FS.M α) (Q : α → FSWorld → Prop)
    (each : ∀p,p.head=head→p.tail=tail→Spec pid head tail (next p) Q) :
    Spec pid head tail (getPipe pid >>= next) Q := by
  intro f t a x g u b before hr
  cases hp : f.pipes[pid]? with
  | none => simp [getPipe,hp] at hr
  | some p =>
    simp [ends,hp] at before
    simp only [run_bind] at hr
    simp [getPipe,hp] at hr
    exact each p before.1 before.2 _ _ _ _ _ _ _ (by simp [ends,hp,before]) hr

theorem spec_update {α : Type} (pid : PipeId) (head tail : UInt32) (i : Nat)
    (next : UInt32 → FS.M α) (Q : α → FSWorld → Prop)
    (each : Spec pid head (tail+1) (next (tail+1)) Q) :
    Spec pid head tail (pipeUpdateTail pid i tail >>= next) Q := by
  intro f t a x g u b before hr
  rw [run_bind] at hr
  cases he : run (pipeUpdateTail pid i tail) f t a with
  | error e => simp [he] at hr
  | ok pair =>
    rcases pair with ⟨⟨⟨out,m⟩,v⟩,c⟩
    obtain ⟨rfl,kept⟩:=update_ends pid i tail head f m t v a c out before he
    simp only [he,ok_bind] at hr
    exact each m v c x g u b kept hr

def Progress (pid : PipeId) (initial : Nat) (out : ForInStep (Nat × Int)) (f : FSWorld) : Prop :=
  match out with
  | .done _ => True
  | .yield s => ∃head tail,ends pid f=some (head,tail) ∧ s.1+pipeOccupancy head tail<initial

theorem blocked_progress (iocb : Kiocb) (filp : File) (pid : PipeId) (state : Nat × Int)
    (head tail : UInt32) (initial : Nat) :
    Spec pid head tail (blocked iocb filp pid state) (Progress pid initial) := by
  unfold blocked
  repeat' first
    | with_reducible apply spec_cmp
    | with_reducible exact spec_bad_bind _ _ _ _ _ _
    | (with_reducible apply spec_pure; intro f hf; simp only [Progress])
    | (with_reducible apply framed_bind; exact frame_getPipe _ _)
    | with_reducible apply spec_pure_bind
    | split
    | (with_reducible intro x; try dsimp only)


theorem spec_done (pid : PipeId) (head tail : UInt32) (initial : Nat) (state : Nat × Int) :
    Spec pid head tail (pure (.done state)) (Progress pid initial) :=
  spec_pure _ _ _ _ _ (fun _ _=>True.intro)

theorem spec_yield (pid : PipeId) (head tail : UInt32) (initial : Nat) (state : Nat × Int)
    (smaller : state.1+pipeOccupancy head tail<initial) :
    Spec pid head tail (pure (.yield state)) (Progress pid initial) :=
  spec_pure _ _ _ _ _ (fun _ hf=>⟨head,tail,hf,smaller⟩)

theorem finish_progress (iocb : Kiocb) (filp : File) (pid : PipeId)
    (head tail : UInt32) (i start total : Nat) (ret : Int) (buf : PipeBuffer) (chars : Nat)
    (ne : head≠tail) (bound : total≤start) (zero : chars=0→buf.len=0 ∨ start=0) :
    Spec pid head tail (finishItem iocb filp pid head tail i total ret buf chars)
      (Progress pid (start+pipeOccupancy head tail)) := by
  unfold finishItem
  dsimp only
  with_reducible apply framed_bind _ _ _ _ _ _ (frame_setBuf pid i buf)
  intro _
  with_reducible apply spec_branch
  by_cases empty : buf.len=0
  · simp only [empty,beq_self_eq_true,ite_true]
    with_reducible apply spec_update
    have dec:=occupancy_step head tail ne
    repeat' first
      | with_reducible apply spec_branch
      | with_reducible apply spec_cmp
      | with_reducible exact spec_done _ _ _ _ _
      | (with_reducible apply spec_yield; dsimp only; simp_all only [beq_iff_eq] <;> omega)
      | with_reducible exact blocked_progress _ _ _ _ _ _ _
      | split
  · have nonzero : 0<chars ∨ start=0 := by
      by_cases h : chars=0
      · exact Or.inr ((zero h).resolve_left empty)
      · exact Or.inl (by omega)
    simp only [show (buf.len==0)=false from by simp [empty],Bool.false_eq_true,ite_false]
    repeat' first
      | with_reducible apply spec_branch
      | with_reducible apply spec_cmp
      | with_reducible exact spec_done _ _ _ _ _
      | (with_reducible apply spec_yield; dsimp only; simp_all only [beq_iff_eq] <;> omega)
      | with_reducible exact blocked_progress _ _ _ _ _ _ _
      | split


theorem copy_progress (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat)
    (head tail : UInt32) (i : Nat) (state : Nat × Int) (buf : PipeBuffer) (chars : Nat)
    (ne : head≠tail) (bound : chars≤state.1) (zero : chars=0→buf.len=0 ∨ state.1=0) :
    Spec pid head tail (copyItem iocb filp pid count head tail i state buf chars)
      (Progress pid (state.1+pipeOccupancy head tail)) := by
  unfold copyItem
  repeat' first
    | with_reducible apply spec_branch
    | with_reducible apply spec_cmp
    | with_reducible exact spec_bad_bind _ _ _ _ _ _
    | with_reducible exact spec_invariant _ _ _ _ _
    | with_reducible exact spec_done _ _ _ _ _
    | (with_reducible apply framed_bind; exact frame_confirm _ _)
    | (with_reducible apply framed_bind; exact frame_copy _ _ _ _ _)
    | (with_reducible apply finish_progress; exact ne; omega; intro h; simp_all only [Nat.sub_zero,true_or])
    | split
    | (with_reducible intro x; try dsimp only)
    | (dsimp only; split)


theorem step_progress (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat)
    (head tail : UInt32) (state : Nat × Int) :
    Spec pid head tail (step iocb filp pid count state)
      (Progress pid (state.1+pipeOccupancy head tail)) := by
  unfold step
  with_reducible apply spec_read
  intro p hh ht
  dsimp only
  rw [hh,ht]
  with_reducible apply spec_cmp
  by_cases ne : head≠tail
  · simp only [show (head != tail)=true from by simp [ne],ite_true]
    repeat' first
      | with_reducible apply spec_cmp
      | with_reducible exact spec_bad_bind _ _ _ _ _ _
      | (with_reducible apply framed_bind; exact frame_idx _ _ _)
      | (with_reducible apply framed_bind; exact frame_getBuf _ _)
      | split
      | (with_reducible intro x; try dsimp only)
    all_goals
      with_reducible apply copy_progress
      · exact ne
      · simp_all only [decide_eq_true_eq] <;> omega
      · intro h; simp_all
  · simp only [show (head != tail)=false from by simp [Classical.byContradiction ne],Bool.false_eq_true,ite_false]
    exact blocked_progress _ _ _ _ _ _ _


def measure (pid : PipeId) (state : Nat × Int) (f : FSWorld) : Nat :=
  state.1 + ((ends pid f).map (fun e=>pipeOccupancy e.1 e.2)).getD 0

theorem step_yield (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat)
    (state next : Nat × Int) (f g : FSWorld) (t u : TaskWorld) (a b : Ambient)
    (hr : run (step iocb filp pid count state) f t a=.ok (((.yield next,g),u),b)) :
    measure pid next g < measure pid state f := by
  cases hp : f.pipes[pid]? with
  | none => simp [step,getPipe,hp] at hr
  | some p =>
    have progress := step_progress iocb filp pid count p.head p.tail state f t a
      (.yield next) g u b (by simp [ends,hp]) hr
    obtain ⟨head,tail,hfinal,smaller⟩:=progress
    unfold measure
    rw [hfinal]
    simpa only [ends,hp,Option.map_some,Option.getD_some] using smaller

def evaluate (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat) :
    Nat → Nat × Int → FS.M (Nat × Int)
  | 0,_ => invariant "proof-side pipe-read fuel exhausted"
  | fuel+1,state => do
    match ← step iocb filp pid count state with
    | .done next => pure next
    | .yield next => evaluate iocb filp pid count fuel next

def finite (iocb : Kiocb) (count : Nat) : FS.M Int :=
  withLoop (fun filp pid state=>do
    let f ← get
    evaluate iocb filp pid count (measure pid state f+1) state) iocb count

theorem loop_unfold (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat) (state : Nat × Int) :
    loop iocb filp pid count state = (do
      match ← step iocb filp pid count state with
      | .done next => pure next
      | .yield next => loop iocb filp pid count next) := by
  unfold loop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  apply bind_congr
  intro out
  cases out <;> rfl

theorem loop_finite (iocb : Kiocb) (filp : File) (pid : PipeId) (count fuel : Nat)
    (state : Nat × Int) (f : FSWorld) (t : TaskWorld) (a : Ambient)
    (enough : measure pid state f<fuel) :
    run (loop iocb filp pid count state) f t a =
      run (evaluate iocb filp pid count fuel state) f t a := by
  induction fuel generalizing state f t a with
  | zero => omega
  | succ fuel ih =>
    rw [loop_unfold,evaluate]
    simp only [run_bind]
    cases he : run (step iocb filp pid count state) f t a with
    | error e => rfl
    | ok pair =>
      rcases pair with ⟨⟨⟨out,g⟩,u⟩,b⟩
      simp only [ok_bind]
      cases out with
      | done next => rfl
      | yield next =>
        have smaller:=step_yield iocb filp pid count state next f g t u a b he
        apply ih
        omega

theorem finite_source (iocb : Kiocb) (count : Nat) :
    pipeRead iocb count=finite iocb count := by
  rw [original_source]
  unfold finite
  congr 1
  funext filp pid state f t a
  change run (loop iocb filp pid count state) f t a =
    run (do let w ← get; evaluate iocb filp pid count (measure pid state w+1) state) f t a
  simp only [run_bind,run_get,ok_bind]
  exact loop_finite iocb filp pid count (measure pid state f+1) state f t a (by omega)

end Leanux.Proofs.WG.Progress.PipeRead
