import Leanux.Proofs.WG.Progress.PipeFreeFrames
import Init.Internal.Order.While

/-! Exact finite evaluation of freePipeInfo. The fuel bound counts the stopping
test and decreases on each actual yield. All original failures, accounting,
branch records, buffer releases and final page/store effects are preserved. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PipeFree
open Leanux

def step (pid : PipeId) (i : Nat) : FS.M (ForInStep Nat) := do
  let p ← getPipe pid
  if !(← branch .freePipeInfoLoop (i < p.ringSize)) then return .done i
  if ← branch .freePipeInfoBufOps (← getPipeBuf pid i).ops then
    pipeBufRelease pid i
  return .yield (i+1)

def loop (pid : PipeId) (i : Nat) : FS.M Nat :=
  Lean.Loop.forIn Lean.Loop.mk i (fun _ i=>step pid i)

def evaluate (pid : PipeId) : Nat → Nat → FS.M Nat
  | 0, _ => invariant "proof-side pipe-free fuel exhausted"
  | fuel+1,i => do
    match ← step pid i with
    | .done j => pure j
    | .yield j => evaluate pid fuel j

def finish (pid : PipeId) : FS.M Unit := do
  if let some page := (← getPipe pid).tmpPage then
    _ ← branch .freePipeInfoTmpPage true
    putPipePage page
  else
    _ ← branch .freePipeInfoTmpPage false
  modify fun f=>{f with pipes:=f.pipes.erase pid}

def finite (pid : PipeId) : FS.M Unit := do
  _ ← accountPipeBuffers (← getPipe pid).nrAccounted 0
  let bound := ((← get).pipes[pid]?).map (·.ringSize) |>.getD 0
  _ ← evaluate pid (bound+1) 0
  finish pid

theorem original_source (pid : PipeId) :
    freePipeInfo pid = (do
      _ ← accountPipeBuffers (← getPipe pid).nrAccounted 0
      _ ← loop pid 0
      finish pid) := rfl

theorem loop_unfold (pid : PipeId) (i : Nat) :
    loop pid i = (do
      match ← step pid i with
      | .done j => pure j
      | .yield j => loop pid j) := by
  unfold loop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  apply bind_congr
  intro s
  cases s <;> rfl

theorem step_yield (pid : PipeId) (i j : Nat) (f g : FSWorld)
    (t u : TaskWorld) (a b : Ambient)
    (hr : run (step pid i) f t a = .ok ((((.yield j),g),u),b)) :
    rings pid g = rings pid f ∧ j=i+1 ∧ i < (rings pid f).getD 0 := by
  cases hp : f.pipes[pid]? with
  | none => simp [step,getPipe,hp] at hr
  | some p =>
    by_cases bound : i<p.ringSize
    · simp [step,getPipe,hp,bound,getPipeBuf,show ¬p.ringSize≤i from by omega] at hr
      cases hb : p.bufs[i]? with
      | none => simp [hb] at hr
      | some buf =>
        cases ops : buf.ops
        · simp [hb,ops] at hr
          rcases hr with ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
          exact ⟨rfl,rfl,by simpa [rings,hp] using bound⟩
        · simp [hb,ops] at hr
          cases he : run (pipeBufRelease pid i) f t
              ({a with steps:=a.steps.push {decision:=.freePipeInfoLoop,outcome:=true,netRx:=a.netRxSection}}
                |> fun c=>{c with steps:=c.steps.push {decision:=.freePipeInfoBufOps,outcome:=true,netRx:=c.netRxSection}}) with
          | error e => simp [he] at hr; cases hr
          | ok v =>
            rcases v with ⟨⟨⟨v,g'⟩,u'⟩,b'⟩
            cases v
            simp [he] at hr
            rcases hr with ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
            exact ⟨release_ring pid i f g' t u' _ b' he,rfl,by simpa [rings,hp] using bound⟩
    · simp [step,getPipe,hp,bound,show p.ringSize≤i from by omega] at hr


theorem loop_finite (pid : PipeId) (fuel i : Nat) (f : FSWorld)
    (t : TaskWorld) (a : Ambient)
    (enough : (rings pid f).getD 0-i<fuel) :
    run (loop pid i) f t a = run (evaluate pid fuel i) f t a := by
  induction fuel generalizing i f t a with
  | zero => omega
  | succ fuel ih =>
    rw [loop_unfold,evaluate]
    simp only [run_bind]
    cases he : run (step pid i) f t a with
    | error e => rfl
    | ok v =>
      rcases v with ⟨⟨⟨s,g⟩,u⟩,b⟩
      simp only [ok_bind]
      cases s with
      | done j => rfl
      | yield j =>
        obtain ⟨same,rfl,below⟩:=step_yield pid i j f g t u a b he
        apply ih
        rw [same]
        omega

theorem finite_source (pid : PipeId) : freePipeInfo pid = finite pid := by
  rw [original_source]
  unfold finite
  apply bind_congr
  intro p
  apply bind_congr
  intro count
  funext f t a
  change run (do let _ ← loop pid 0; finish pid) f t a =
    run (do let bound := ((← get).pipes[pid]?).map (·.ringSize) |>.getD 0
            let _ ← evaluate pid (bound+1) 0
            finish pid) f t a
  simp only [run_bind,run_get,ok_bind]
  rw [loop_finite pid ((rings pid f).getD 0+1) 0 f t a (by omega)]
  rfl

end Leanux.Proofs.WG.Progress.PipeFree
