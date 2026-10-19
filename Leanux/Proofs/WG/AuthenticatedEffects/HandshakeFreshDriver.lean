import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFreshWorker
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeDriver
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryReceive

/-! The actual shared driver's session/keepalive helpers do not insert a new
handshake admission. The complete handshake actor can therefore retain the
native receiver's newest-admission relationship without an arbitrary callback
quietness assumption in its initialized conclusion. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh.DriverProof
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeCausal

private def quietHooks : Driver.Hooks Event :=
  {HandshakeDriver.hooks with handshake := fun _ _ => pure false}

private theorem quiet (Good : List Event → Prop) : Driver.HooksHistorySafe Good quietHooks := by
  constructor
  all_goals intros
  all_goals first
    | assumption
    | (rw [Driver.sendWorker_lift quietHooks rfl]; exact Driver.History.product_lift _)
    | exact Driver.History.state_lift _
    | exact Driver.History.state_pure _
    | exact Driver.History.product_lift _
    | exact Driver.History.product_state (Driver.History.state_lift _)
    | exact Driver.History.product_pure _

theorem keepalive_preserves (pid : PeerId) :
    Preserves (Driver.keepaliveObserved HandshakeDriver.hooks pid) :=
  Driver.keepalive_history (g := quietHooks) (quiet Safe) pid

theorem keepalive_frame (pid : PeerId) :
    StateHistoryFrame admission (Driver.keepaliveObserved HandshakeDriver.hooks pid) := by
  intro w a history
  have contract := Driver.keepalive_history (g := quietHooks) (quiet (fun h => h = history)) pid
  obtain ⟨_,_,same,_⟩ := contract w a history rfl
  exact congrArg (List.filterMap admission) same

theorem handshake_complete : Preserves (Driver.handshakeObserved HandshakeDriver.hooks) :=
  Worker.observed_preserves HandshakeDriver.hooks.session
    (Driver.keepaliveObserved HandshakeDriver.hooks)
    (fun _ => Driver.History.state_lift _) keepalive_preserves
    (fun _ _ _ _ => rfl) keepalive_frame


theorem core : Driver.ActorCoreHistorySafe Safe HandshakeDriver.hooks where
  stagedPurge := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  peerRelease := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  deliver := Driver.History.product_lift _
  keepalivePrepare := fun _ => TransmitSecurity.Driver.History.state_lift _
  staging := Driver.staging_history (g := quietHooks) (quiet Safe)
  fixtureEnter := (quiet Safe).fixtureEnter
  fixtureLeave := (quiet Safe).fixtureLeave
  handshake := handshake_complete
  sendWorker := (quiet Safe).sendWorker
  flushedSend := (quiet Safe).flushedSend
  armTimer := (quiet Safe).armTimer
  queueSend := (quiet Safe).queueSend
  candidateEnter := (quiet Safe).candidateEnter
  candidateLeave := (quiet Safe).candidateLeave
  prepare := (quiet Safe).prepare
  counterCheck := (quiet Safe).counterCheck
  timerSelected := (quiet Safe).timerSelected
  timerFinished := (quiet Safe).timerFinished
  confirmation := (quiet Safe).confirmation
  session := (quiet Safe).session
  front := (quiet Safe).front
  poll := (quiet Safe).poll
  encrypt := (quiet Safe).encrypt
  transmit := (quiet Safe).transmit

theorem actors : Driver.ActorHistorySafe Safe HandshakeDriver.hooks :=
  core.withPoll (fun _ _ preserves => preserves)

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh.DriverProof
