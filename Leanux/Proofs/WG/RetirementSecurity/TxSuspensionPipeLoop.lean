import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionPipeRelease

/-! The original free-pipe loop retains suspension by its actual ring bound,
not by an assumed fuel or by treating an arbitrary loop as terminating. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues

def pipeFreeStep (pid : PipeId) (i : Nat) : FS.M (ForInStep Nat) := do
  let p←getPipe pid
  if !(←Leanux.branch .freePipeInfoLoop (i<p.ringSize)) then return .done i
  if ←Leanux.branch .freePipeInfoBufOps (←getPipeBuf pid i).ops then pipeBufRelease pid i
  return .yield (i+1)

theorem pipe_read_native (pid : PipeId)
    (run : (((getPipe pid).run s).run t).run a=.ok (((p,v),u),c)) :
    s.pipes[pid]?=some p ∧ v=s ∧ u=t ∧ c=a := by
  cases hp:s.pipes[pid]? with
  | none=>simp [getPipe,hp,Leanux.invariant,AmbientM.invariant] at run; cases run
  | some found=>
    simp [getPipe,hp] at run
    obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩:=run
    exact ⟨rfl,rfl,rfl,rfl⟩

theorem branch_native (d : Decision) (b : Bool)
    (run : (((Leanux.branch d b : FS.M Bool).run s).run t).run a=.ok (((result,v),u),c)) :
    result=b ∧ v=s ∧ u=t := by
  cases run
  exact ⟨rfl,rfl,rfl⟩

theorem buffer_read_native (pid : PipeId) (i : Nat)
    (run : (((getPipeBuf pid i).run s).run t).run a=.ok (((result,v),u),c)) :
    v=s ∧ u=t ∧ c=a := by
  unfold getPipeBuf at run
  rw [fs_bind_ok] at run
  obtain ⟨p,fs,task,ambient,read,tail⟩:=run
  obtain ⟨_,rfl,rfl,rfl⟩:=pipe_read_native pid read
  split at tail
  · cases tail; exact ⟨rfl,rfl,rfl⟩
  · cases tail

theorem pipe_free_step (pid : PipeId) (i : Nat) : Keeps (pipeFreeStep pid i) := by
  nested_suspension_source [pipeFreeStep] using [get_pipe,branch,pipe_buffer,pipe_buffer_release]

theorem pipe_free_step_decreases (pid : PipeId) (i : Nat)
    (run : (((pipeFreeStep pid i).run s).run t).run a=.ok (((.yield next,v),u),c)) :
    pipeRing pid v-next<pipeRing pid s-i := by
  unfold pipeFreeStep at run
  rw [fs_bind_ok] at run
  obtain ⟨p,fs,task,ambient,read,tail⟩:=run
  obtain ⟨resident,fs_eq,task_eq,ambient_eq⟩:=pipe_read_native pid read
  subst fs task ambient
  rw [fs_bind_ok] at tail
  obtain ⟨flag,fs,task,ambient,read,tail⟩:=tail
  obtain ⟨flag_eq,fs_eq,task_eq⟩:=branch_native _ _ read
  subst flag fs task
  have size : pipeRing pid s=p.ringSize := by simp [pipeRing,resident]
  by_cases bound:i<p.ringSize
  · simp only [bound,decide_true,Bool.not_true,Bool.false_eq_true,ite_false] at tail
    rw [fs_bind_ok] at tail
    obtain ⟨buffer,fs,task,ambient',read,tail⟩:=tail
    obtain ⟨fs_eq,task_eq,ambient_eq⟩:=buffer_read_native pid i read
    subst fs task ambient'
    rw [fs_bind_ok] at tail
    obtain ⟨flag,fs,task,ambient',read,tail⟩:=tail
    obtain ⟨flag_eq,fs_eq,task_eq⟩:=branch_native _ _ read
    subst flag fs task
    cases ops:buffer.ops <;> simp only [ops,Bool.false_eq_true,ite_false,ite_true] at tail
    · cases tail
      omega
    · rw [fs_bind_ok] at tail
      obtain ⟨result,fs,task,ambient'',release,tail⟩:=tail
      have retained := (fs_hoare_iff _ _ _).mp (pipe_buffer_release_ring pid i (pipeRing pid s))
        s t ambient' result fs task ambient'' rfl release
      cases tail
      omega
  · simp only [bound,decide_false,Bool.not_false,ite_true] at tail
    cases tail

theorem pipe_free_loop (pid : PipeId) (start : Nat) :
    Keeps (forIn ({} : Lean.Loop) start (fun _ i=>pipeFreeStep pid i)) :=
  loop _ (fun i s=>pipeRing pid s-i) (pipe_free_step pid)
    (fun i _ _ _ _ _ _ _ run=>pipe_free_step_decreases pid i run) start

theorem pipe_buffers_account (old new : Nat) : Keeps (accountPipeBuffers old new) := by
  nested_suspension_source [accountPipeBuffers] using [invariant]

theorem pipe_free (pid : PipeId) : Keeps (freePipeInfo pid) := by
  unfold freePipeInfo
  repeat' first
    | env_operation_fact get_pipe
    | env_operation_fact pipe_buffers_account
    | env_operation_fact branch
    | env_operation_fact pipe_page_put
    | (nested_suspension_head ForIn.forIn
       change Keeps (forIn ({} : Lean.Loop) _ (fun _ i=>pipeFreeStep pid i))
       exact pipe_free_loop pid _)
    | nested_suspension_step

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
