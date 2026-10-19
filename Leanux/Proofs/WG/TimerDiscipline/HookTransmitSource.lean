import Leanux.Proofs.WG.TimerDiscipline.HookJournalClaims
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal.Transmit
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- Three caller hook cuts around the existing complete item traversal.
The item step and key-refresh suffix contain no timer-hook invocation. -/
def withHooks {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (hook : Hook → PeerId → m Unit) (pid : PeerId) (items : List SkbId) : m Unit := do
  hook .traversal pid
  hook .authenticatedSent pid
  let sent ← step (forIn items false (dataDoneStep pid))
  _ ← step (branch .doneSkbIterate false)
  if ← step (branch .doneDataSent sent) then hook .dataSent pid
  step (keepKeyFresh pid)

theorem source (pid : PeerId) (items : List SkbId) :
    withHooks (fun {_} a=>a) action pid items = createDataDone pid items := rfl

def observed (pid : PeerId) (items : List SkbId) : WGPrefix Receipt Unit :=
  withHooks (fun {_} a=>liftWGPrefix a) HookJournal.observed pid items

theorem erases (pid : PeerId) (items : List SkbId) :
    ErasesStatePrefix (observed pid items) (createDataDone pid items) := by
  rw [←source]
  unfold observed withHooks
  apply erasesStatePrefix_bind (observed_erases .traversal pid)
  intro _
  apply erasesStatePrefix_bind (observed_erases .authenticatedSent pid)
  intro _
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro sent
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro selected
  cases selected
  · exact erasesStatePrefix_lift _
  · exact erasesStatePrefix_bind (observed_erases .dataSent pid)
      (fun _=>erasesStatePrefix_lift _)

theorem quiet {α : Type} (a : WG.M α) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory
      (liftWGPrefix a : WGPrefix Receipt α) :=
  StatePrefixEnsures.lift a (fun _ _ _ hi=>hi) (fun _ _ _ _ _ _ hi _=>hi)

theorem preserves (pid : PeerId) (items : List SkbId) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (observed pid items) := by
  unfold observed withHooks
  apply (observed_preserves .traversal pid).bind
  intro _
  apply (observed_preserves .authenticatedSent pid).bind
  intro _
  apply (quiet _).bind
  intro sent
  apply (quiet _).bind
  intro _
  apply (quiet _).bind
  intro selected
  cases selected
  · exact quiet _
  · exact (observed_preserves .dataSent pid).bind (fun _=>quiet _)


end Leanux.Proofs.WG.TimerDiscipline.HookJournal.Transmit

