import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerFrames
import Leanux.Proofs.WG.Queues.RxNapiCuts

/-! Native NAPI metadata reads retain the packet-accounting view. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveNapiFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem pending_frame : SameView StagedEntry.view RxNapi.pendingSource := by
  unfold RxNapi.pendingSource
  apply SameView.bind (TimerFrames.store getDev_sameWGStore)
  intro d
  exact SameView.pure _ _

theorem scheduled_frame : SameView StagedEntry.view RxNapi.scheduledSource := by
  unfold RxNapi.scheduledSource
  apply SameView.bind (TimerFrames.store getDev_sameWGStore)
  intro d
  exact SameView.pure _ _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveNapiFrames
