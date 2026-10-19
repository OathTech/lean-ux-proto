import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionTimers

/-! Native work-queue records and data-sent timer maintenance preserve the
actual suspended-activation list used by TX conservation. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem record_queued_ambient (worker : Worker) (pid : PeerId) :
    SameView Ambient.suspended (AmbientM.recordQueued worker pid) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.recordQueued at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  split at tail
  · cases tail; rfl
  · rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨bytes,u,recorded,tail⟩:=tail
    have same: u.suspended=w.suspended :=
      (ProjectedAction.iff_run _ _ _).mp (TxActorFrames.hidden (.queued worker)) w bytes u recorded
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨saved,t,read,tail⟩:=tail
    cases read
    repeat' first
      | (change Except.error _ = Except.ok _ at tail; cases tail)
      | (dsimp +failIfUnchanged only at tail)
      | split at tail
      | (rw [MaterialOrigin.bind_ok] at tail; obtain ⟨x,y,step,tail⟩:=tail; cases step)
      | (cases tail; exact same)

theorem peek_queued_ambient (worker : Worker) (pid : PeerId) :
    SameView Ambient.suspended (AmbientM.peekQueuedUnit worker pid) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.peekQueuedUnit at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  split at tail
  · cases tail; rfl
  · rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨_,u,skipped,tail⟩:=tail
    have same: u.suspended=w.suspended :=
      (ProjectedAction.iff_run _ _ _).mp TxActorFrames.skip w () u skipped
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨saved,t,read,tail⟩:=tail
    cases read
    repeat' first | split at tail | (cases tail; exact same)

theorem record_queued (worker : Worker) (pid : PeerId) :
    Keeps (recordQueued worker pid : StateT S AmbientM Unit) := ambient (record_queued_ambient worker pid)

theorem peek_queued (worker : Worker) (pid : PeerId) :
    Keeps (peekQueuedUnit worker pid : StateT S AmbientM Bool) := ambient (peek_queued_ambient worker pid)

theorem expired (decision : Decision) (birthday : Int64) (seconds : Nat) (f : Bool→Bool) :
    Keeps (branchExpired decision birthday seconds f) := by
  unfold branchExpired birthdateTest
  repeat' first | env_operation_fact clock | env_operation_fact compare | suspension_step

theorem queued_handshake (pid : PeerId) (retry : Bool) : Keeps (sendQueuedHandshakeInitiation pid retry) := by
  suspension_source [sendQueuedHandshakeInitiation] using [expired,branch,peer,peer_get,peer_put,set_peer,device,modify_device,peek_queued,record_queued]

theorem fresh (pid : PeerId) : Keeps (keepKeyFresh pid) := by
  suspension_source [keepKeyFresh,WG.andM,WG.orM] using [invariant,peer,key,branch,compare,expired,queued_handshake]

theorem record_budget : Keeps (recordBudget : StateT S AmbientM Nat) := ambient TxActorFrames.budget

theorem exhausted (message : String) : Keeps (budgetExhausted message : StateT S AmbientM α) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold AmbientM.budgetExhausted at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  split at tail <;> cases tail

theorem jitter (site : HiddenSite) : Keeps (jitterBelowRekeyTimeout site) := by
  unfold jitterBelowRekeyTimeout
  repeat' first | env_operation_fact record_budget | env_operation_fact hidden | env_operation_fact exhausted | suspension_step

theorem data_sent (pid : PeerId) : Keeps (timersDataSent pid) := by
  suspension_source [timersDataSent] using [peer,branch,caller_jiffies,jitter,guard,arm]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
