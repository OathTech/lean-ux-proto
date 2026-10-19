import Leanux.Proofs.WG.TimerDiscipline.HookTransmitSource

/-! Projected exact outcome and reached hook receipts for the original complete encrypted-data completion caller. Earlier receipts survive any later Stop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal.Transmit
open Leanux Leanux.WG Leanux.Proofs.Logged

def inspection (pid : PeerId) (items : List SkbId) :
    WG.M (Campaign2.Outcome Unit × List Receipt) := fun g a =>
  let result := runWGPrefix (observed pid items) g a []
  .ok (((Campaign2.observeResult result.1,result.2),g),a)

theorem inspection_source (pid : PeerId) (items : List SkbId) :
    (do let result←inspection pid items; pure result.1) =
      Campaign2.inspect (createDataDone pid items) := by
  funext g a
  change Except.ok ((Campaign2.observeResult (runWGPrefix (observed pid items) g a []).1,g),a) =
    Except.ok ((Campaign2.observeResult (((createDataDone pid items).run g).run a),g),a)
  dsimp only [runWGPrefix,runStatePrefix]
  rw [erases pid items g a []]

theorem inspection_valid (pid : PeerId) (items : List SkbId) :
    Campaign2.Returns (inspection pid items) (fun _=>True)
      (fun result _=>ValidHistory result.2) := by
  intro g a _
  obtain ⟨_,_,valid,_⟩:=preserves pid items g a [] (by intro r member; cases member)
  exact ⟨_,g,a,rfl,valid⟩

theorem original (pid : PeerId) (items : List SkbId) :
    (do let result←inspection pid items; pure result.1) =
      Campaign2.inspect (createDataDone pid items) ∧
    Campaign2.Returns (inspection pid items) (fun _=>True)
      (fun result _=>∀r∈result.2,r.Valid) :=
  ⟨inspection_source pid items,inspection_valid pid items⟩

end Leanux.Proofs.WG.TimerDiscipline.HookJournal.Transmit

