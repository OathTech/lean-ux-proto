import Leanux.Proofs.WG.TimerDiscipline.HookTransmitWorkerSource

/-! Exact original transmit iteration and retained hook receipts, including
the final packet/key/peer payments and worker reschedule observation. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal.TransmitWorker
open Leanux Leanux.WG Leanux.Proofs.Logged

def inspection (pid : PeerId) :
    Leanux.M (Campaign2.Product.Outcome IterResult × List Receipt) := fun w =>
  let result := runPrefix (iteration pid) w []
  .ok ((Campaign2.Product.observeResult result.1,result.2),w)

theorem inspection_source (pid : PeerId) :
    (do let result←inspection pid; pure result.1) =
      Campaign2.Product.inspect (txIter pid (Env.condResched .txWorker)) := by
  funext w
  change Except.ok (Campaign2.Product.observeResult (runPrefix (iteration pid) w []).1,w) =
    Except.ok (Campaign2.Product.observeResult ((txIter pid (Env.condResched .txWorker)).run w),w)
  rw [iteration_erases pid w []]

theorem inspection_valid (pid : PeerId) :
    Campaign2.Product.Returns (inspection pid) (fun _=>True)
      (fun result _=>ValidHistory result.2) := by
  intro w _
  obtain ⟨_,_,valid,_⟩:=iteration_preserves pid w [] (by intro r member; cases member)
  exact ⟨_,w,rfl,valid⟩

theorem original (pid : PeerId) :
    (do let result←inspection pid; pure result.1) =
      Campaign2.Product.inspect (txIter pid (Env.condResched .txWorker)) ∧
    Campaign2.Product.Returns (inspection pid) (fun _=>True)
      (fun result _=>∀r∈result.2,r.Valid) :=
  ⟨inspection_source pid,inspection_valid pid⟩

end Leanux.Proofs.WG.TimerDiscipline.HookJournal.TransmitWorker
