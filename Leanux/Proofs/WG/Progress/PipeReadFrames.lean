import Leanux.Proofs.WG.Progress.PipeWriteFrames

/-! Physical ring-end transport for the original pipe read leaves. The release
projection reuses the strengthened owned PipeFree frame. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PipeRead
open Leanux PipeFree

def ends (pid : PipeId) (f : FSWorld) : Option (UInt32 × UInt32) :=
  (f.pipes[pid]?).map (fun p=>(p.head,p.tail))
def Frame {α : Type} (pid : PipeId) (action : FS.M α) : Prop :=
  ∀ f t a x g u b, run action f t a = .ok (((x,g),u),b) → ends pid g=ends pid f

theorem frame_getPipe (pid q : PipeId) : Frame pid (getPipe q) := by
  intro f t a x g u b hr
  cases h : f.pipes[q]? <;> simp [getPipe,h] at hr
  obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩:=hr
  rfl

theorem frame_idx (pid : PipeId) (p : PipeInodeInfo) (i : UInt32) :
    Frame pid (pipeBufIdx p i) := by
  intro f t a x g u b hr
  by_cases bad : (p.ringSize == 0 || p.bufs.size != p.ringSize)=true
  · simp [pipeBufIdx,bad] at hr
    cases hr
  · simp [pipeBufIdx,bad] at hr
    exact congrArg (ends pid) hr.1.1.2.symm

theorem frame_getBuf (pid : PipeId) (i : Nat) : Frame pid (getPipeBuf pid i) := by
  intro f t a x g u b hr
  cases hp : f.pipes[pid]? <;> simp [getPipeBuf,getPipe,hp] at hr
  rename_i p
  cases hb : p.bufs[i]? <;> simp [hb] at hr
  obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩:=hr
  rfl

theorem frame_setBuf (pid : PipeId) (i : Nat) (buf : PipeBuffer) :
    Frame pid (setPipeBuf pid i buf) := by
  intro f t a x g u b hr
  cases hp : f.pipes[pid]? <;> simp [setPipeBuf,getPipe,hp] at hr
  rename_i p
  by_cases bound : i<p.bufs.size
  all_goals simp [bound,setPipe] at hr
  obtain ⟨⟨rfl,rfl⟩,rfl⟩:=hr
  simp [ends,hp]

theorem frame_confirm (pid : PipeId) (buf : PipeBuffer) :
    Frame pid (pipeBufConfirm buf) := by
  intro f t a x g u b hr
  cases hb : buf.ops <;> simp [pipeBufConfirm,hb] at hr
  obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩:=hr
  rfl

theorem frame_copy (pid : PipeId) (page : PageId) (offset bytes cap : Nat) :
    Frame pid (copyPageToIter page offset bytes cap) := by
  intro f t a x g u b hr
  cases he : (AmbientM.envOk .copyPageToIter).run a with
  | error e => simp [copyPageToIter,he] at hr
  | ok pair =>
    obtain ⟨ok,a'⟩:=pair
    cases ok
    · simp [copyPageToIter,he] at hr
      obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩:=hr
      rfl
    · simp [copyPageToIter,he,getPage] at hr
      cases pg : f.pages[page]? with
      | none => simp [pg] at hr
      | some p =>
        by_cases bound : offset+min bytes (cap-(f.userOut.getD ByteArray.empty).size)>p.bytes.size
        all_goals simp [pg,bound] at hr
        obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩:=hr
        rfl

theorem release_ends (pid : PipeId) (i : Nat) : Frame pid (pipeBufRelease pid i) := by
  intro f t a x g u b hr
  cases x
  have h:=release_shape pid i f g t u a b hr
  have projected:=congrArg (Option.map Prod.snd) h
  simpa only [shape,ends,Option.map_map,Function.comp_def] using projected

theorem update_ends (pid : PipeId) (i : Nat) (tail head : UInt32)
    (f g : FSWorld) (t u : TaskWorld) (a b : Ambient) (out : UInt32)
    (before : ends pid f=some (head,tail))
    (hr : run (pipeUpdateTail pid i tail) f t a=.ok (((out,g),u),b)) :
    out=tail+1 ∧ ends pid g=some (head,tail+1) := by
  simp only [pipeUpdateTail,run_bind] at hr
  cases he : run (pipeBufRelease pid i) f t a with
  | error e => simp [he] at hr
  | ok pair =>
    rcases pair with ⟨⟨⟨value,middle⟩,tasks⟩,ambient⟩
    cases value
    have kept:ends pid middle=some (head,tail):=
      (release_ends pid i f t a () middle tasks ambient he).trans before
    simp only [he,ok_bind] at hr
    cases hp : middle.pipes[pid]? with
    | none => simp [getPipe,hp] at hr
    | some p =>
      simp [ends,hp] at kept
      obtain ⟨rfl,rfl⟩:=kept
      simp [getPipe,hp,setPipe] at hr
      rcases hr with ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
      exact ⟨rfl,by simp [ends]⟩


end Leanux.Proofs.WG.Progress.PipeRead
