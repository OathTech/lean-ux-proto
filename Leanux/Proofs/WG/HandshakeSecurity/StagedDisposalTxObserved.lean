import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalTxFocus

/-! Actual nested TX release observation, ready for the same final journal.
Projection preserves all old packet/lifetime events and the first Stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.TxSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues AuthenticatedEffects

def observed (encode : TxDisposition.Event → E) (decode : E → Option TxDisposition.Event)
    (record : Event → E) : Ops E :=
  {Ops.focus encode decode native with release := releaseObserved encode decode record}

theorem focused_matching (ρ : E → Option F)
    (eg : TxDisposition.Event → E) (dg : E → Option TxDisposition.Event)
    (et : TxDisposition.Event → F) (dt : F → Option TxDisposition.Event)
    (enc : ∀ event, ρ (eg event) = some (et event))
    (dec : ∀ event, dg event = (ρ event).bind dt) :
    Ops.Projects ρ (Ops.focus eg dg native) (Ops.focus et dt native) := by
  constructor
  all_goals intros
  all_goals exact CompletionEffects.focus_matching ρ eg dg et dt enc dec _

theorem observed_matching (ρ : E → Option F)
    (eg : TxDisposition.Event → E) (dg : E → Option TxDisposition.Event)
    (et : TxDisposition.Event → F) (dt : F → Option TxDisposition.Event)
    (enc : ∀ event, ρ (eg event) = some (et event))
    (dec : ∀ event, dg event = (ρ event).bind dt)
    (inverse : ∀ event, dt (et event) = some event)
    (record : Event → E) (quiet : ∀ event, ρ (record event) = none) :
    Ops.Projects ρ (observed eg dg record) (Ops.focus et dt native) :=
  {focused_matching ρ eg dg et dt enc dec with
    release := release_matching ρ eg dg et dt enc dec inverse record quiet}

variable (ρ : E → Option F)
  (eg : TxDisposition.Event → E) (dg : E → Option TxDisposition.Event)
  (et : TxDisposition.Event → F) (dt : F → Option TxDisposition.Event)
  (enc : ∀ event, ρ (eg event) = some (et event))
  (dec : ∀ event, dg event = (ρ event).bind dt)
  (inverse : ∀ event, dt (et event) = some event)
  (record : Event → E) (quiet : ∀ event, ρ (record event) = none)

include enc dec inverse quiet

theorem publish_observed_projects (item : List SkbId) (state : PacketState) :
    ProjectsPrefix ρ id (publish (observed eg dg record) item state)
      (focusPrefix et dt (TxDisposition.publish item state)) := by
  rw [← publish_native,← publish_focus et dt inverse native native_appends]
  exact publish_projects ρ (observed_matching ρ eg dg et dt enc dec inverse record quiet) item state

theorem create_observed_projects (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix ρ id (create (observed eg dg record) pid item)
      (focusPrefix et dt (TxDisposition.create pid item)) := by
  rw [← create_native,← create_focus et dt inverse native native_appends]
  exact create_projects ρ (observed_matching ρ eg dg et dt enc dec inverse record quiet) pid item

theorem dispose_observed_projects (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ProjectsPrefix ρ id (dispose (observed eg dg record) pid item key)
      (focusPrefix et dt (TxDisposition.dispose pid item key)) := by
  rw [← dispose_native,← dispose_focus et dt inverse native native_appends]
  exact dispose_projects ρ (observed_matching ρ eg dg et dt enc dec inverse record quiet) pid item key

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.TxSource
