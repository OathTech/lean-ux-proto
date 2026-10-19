import Leanux.Proofs.WG.TimerDiscipline.HookInitiationSource

/-! Projected whole initiation sender and worker inspections. Exact original
outcomes are preserved, including Stops; receipts do not assert successful
network delivery or whole-driver invocation completeness. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal.Initiation
open Leanux Leanux.WG Leanux.Proofs.Logged

def inspection (pid : PeerId) :
    WG.M (Campaign2.Outcome Unit × List Receipt) := fun g a =>
  let result := runWGPrefix (observed pid) g a []
  .ok (((Campaign2.observeResult result.1,result.2),g),a)

theorem inspection_source (pid : PeerId) :
    (do let result←inspection pid; pure result.1) =
      Campaign2.inspect (sendHandshakeInitiation pid) := by
  funext g a
  change Except.ok ((Campaign2.observeResult (runWGPrefix (observed pid) g a []).1,g),a) =
    Except.ok ((Campaign2.observeResult (((sendHandshakeInitiation pid).run g).run a),g),a)
  dsimp only [runWGPrefix,runStatePrefix]
  rw [erases pid g a []]

theorem inspection_valid (pid : PeerId) :
    Campaign2.Returns (inspection pid) (fun _=>True)
      (fun result _=>ValidHistory result.2) := by
  intro g a _
  obtain ⟨_,_,valid,_⟩:=preserves pid g a [] (by intro r member; cases member)
  exact ⟨_,g,a,rfl,valid⟩

/-- Exact original outcome and valid receipts for each reached hook in the
defined caller observer. A failed hook also has a receipt; later Stops keep
earlier receipts. This does not assert successful network delivery. -/
theorem original (pid : PeerId) :
    (do let result←inspection pid; pure result.1) =
      Campaign2.inspect (sendHandshakeInitiation pid) ∧
    Campaign2.Returns (inspection pid) (fun _=>True)
      (fun result _=>∀r∈result.2,r.Valid) :=
  ⟨inspection_source pid,inspection_valid pid⟩

def workerInspection (pid : PeerId) :
    WG.M (Campaign2.Outcome Unit × List Receipt) := fun g a =>
  let result := runWGPrefix (workerObserved pid) g a []
  .ok (((Campaign2.observeResult result.1,result.2),g),a)

theorem worker_inspection_source (pid : PeerId) :
    (do let result←workerInspection pid; pure result.1) =
      Campaign2.inspect (handshakeSendWorker pid) := by
  funext g a
  change Except.ok ((Campaign2.observeResult (runWGPrefix (workerObserved pid) g a []).1,g),a) =
    Except.ok ((Campaign2.observeResult (((handshakeSendWorker pid).run g).run a),g),a)
  dsimp only [runWGPrefix,runStatePrefix]
  rw [worker_erases pid g a []]

theorem worker_inspection_valid (pid : PeerId) :
    Campaign2.Returns (workerInspection pid) (fun _=>True)
      (fun result _=>ValidHistory result.2) := by
  intro g a _
  obtain ⟨_,_,valid,_⟩:=worker_preserves pid g a [] (by intro r member; cases member)
  exact ⟨_,g,a,rfl,valid⟩

theorem original_worker (pid : PeerId) :
    (do let result←workerInspection pid; pure result.1) =
      Campaign2.inspect (handshakeSendWorker pid) ∧
    Campaign2.Returns (workerInspection pid) (fun _=>True)
      (fun result _=>∀r∈result.2,r.Valid) :=
  ⟨worker_inspection_source pid,worker_inspection_valid pid⟩

/-- The worker's payment cannot hide a reached initiation hook, even if
that payment fails after all three hooks have already run. -/
theorem worker_journal_source (pid : PeerId) :
    (do let result←workerInspection pid; pure result.2) =
      (do let result←inspection pid; pure result.2) := by
  funext g a
  change Except.ok (((runWGPrefix (workerObserved pid) g a []).2,g),a) =
    Except.ok (((runWGPrefix (observed pid) g a []).2,g),a)
  rw [worker_history]

end Leanux.Proofs.WG.TimerDiscipline.HookJournal.Initiation
