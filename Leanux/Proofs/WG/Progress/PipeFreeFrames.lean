import Leanux.FS.Pipe
import Leanux.Proofs.WG.Noise.Execution

/-! Actual FS execution equations and the ring-size frame for the original
buffer release, including both the temporary-page cache and page-put paths. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PipeFree
open Leanux

def run {α : Type} (action : FS.M α) (f : FSWorld) (t : TaskWorld) (a : Ambient) :=
  ((action.run f).run t).run a
@[simp] theorem run_bind {α β : Type} (action : FS.M α) (next : α → FS.M β) (f t a) :
    run (action >>= next) f t a =
    (run action f t a >>= fun (((x,g),u),b)=>run (next x) g u b) := rfl
@[simp] theorem run_pure {α : Type} (x : α) (f t a) :
    run (pure x) f t a = .ok (((x,f),t),a) := rfl
@[simp] theorem run_get (f t a) :
    run (get : FS.M FSWorld) f t a = .ok (((f,f),t),a) := rfl
@[simp] theorem run_modify (fn : FSWorld → FSWorld) (f t a) :
    run (modify fn : FS.M Unit) f t a = .ok ((((),fn f),t),a) := rfl
@[simp] theorem run_invariant {α : Type} (s : String) (f t a) :
    run (invariant s : FS.M α) f t a = .error (.invariant s) := rfl
@[simp] theorem run_branch (d : Decision) (v : Bool) (f t a) :
    run (branch d v : FS.M Bool) f t a =
    .ok (((v,f),t),{a with steps:=a.steps.push {decision:=d,outcome:=v,netRx:=a.netRxSection}}) := rfl
@[simp] theorem run_cmp (d : Decision) (v : Bool) (n m : Int) (f t a) :
    run (branchCmp d v n m : FS.M Bool) f t a =
    .ok (((v,f),t),{a with steps:=a.steps.push {decision:=d,outcome:=v,operands:=some (n,m),netRx:=a.netRxSection}}) := rfl
@[simp] theorem ok_bind {α β : Type} (x : α) (f : α → Except Stop β) :
    (Except.ok x >>= f) = f x := rfl
@[simp] theorem error_bind {α β : Type} (e : Stop) (f : α → Except Stop β) :
    (Except.error e >>= f) = .error e := rfl
@[simp] theorem run_map {α β : Type} (fn : α → β) (action : FS.M α) (f t a) :
    run (fn <$> action) f t a =
      (run action f t a >>= fun (((x,g),u),b)=>pure (((fn x,g),u),b)) := rfl
def rings (pid : PipeId) (f : FSWorld) : Option Nat := (f.pipes[pid]?).map (·.ringSize)

def shape (pid : PipeId) (f : FSWorld) : Option (Nat × UInt32 × UInt32) :=
  (f.pipes[pid]?).map (fun p=>(p.ringSize,p.head,p.tail))
theorem release_shape (pid : PipeId) (i : Nat) (f f' : FSWorld)
    (t t' : TaskWorld) (a a' : Ambient)
    (hr : run (pipeBufRelease pid i) f t a = .ok ((((),f'),t'),a')) :
    shape pid f' = shape pid f := by
  cases hp : f.pipes[pid]? with
  | none => simp [pipeBufRelease,getPipeBuf,getPipe,hp] at hr
  | some p =>
    cases hb : p.bufs[i]? with
    | none => simp [pipeBufRelease,getPipeBuf,getPipe,hp,hb] at hr
    | some buf =>
      cases hops : buf.ops <;>
        simp [pipeBufRelease,getPipeBuf,getPipe,hp,hb,hops] at hr
      by_cases bound : i < p.bufs.size <;>
        simp [setPipeBuf,getPipe,setPipe,hp,bound] at hr
      cases hpage : buf.page with
      | none => simp [anonPipeBufRelease,hpage] at hr
      | some page =>
        cases hpg : f.pages[page]? with
        | none => simp [anonPipeBufRelease,hpage,getPage,hpg] at hr
        | some pg =>
          by_cases one : pg.pageCount=1
          all_goals simp [anonPipeBufRelease,hpage,getPage,hpg,one,getPipe] at hr
          · cases htmp : p.tmpPage
            all_goals simp [htmp,setPipe,putPipePage,getPage,hpg,one] at hr
            all_goals rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩
            all_goals simp [shape,hp]
          · by_cases zero : pg.pageCount=0
            all_goals simp [putPipePage,getPage,hpg,one,zero,setPage] at hr
            rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩
            simp [shape,hp]



theorem release_ring (pid : PipeId) (i : Nat) (f f' : FSWorld)
    (t t' : TaskWorld) (a a' : Ambient)
    (hr : run (pipeBufRelease pid i) f t a = .ok ((((),f'),t'),a')) :
    rings pid f' = rings pid f := by
  have kept:=release_shape pid i f f' t t' a a' hr
  have projected:=congrArg (Option.map Prod.fst) kept
  simpa only [shape,rings,Option.map_map,Function.comp_def] using projected

end Leanux.Proofs.WG.Progress.PipeFree
