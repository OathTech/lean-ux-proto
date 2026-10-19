import Leanux.Proofs.WG.AuthenticatedEffects.CausalStackHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CausalStackSend
import Leanux.Proofs.WG.AuthenticatedEffects.CausalStackCompletion
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryReceive

/-! Ordinary actors preserve stack-origin history. The actual native poll is
kept separate because only it establishes a newly delivered occurrence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.StackOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

private theorem old_state (body : WGPrefix Journal.Event α) :
    Driver.StateHistorySafe Safe (state body) := quiet_state Event.old old? (fun _ => rfl) body

private theorem old_product (body : PrefixM Journal.Event α) :
    Driver.ProductHistorySafe Safe (product body) := quiet_product Event.old old? (fun _ => rfl) body

private theorem session (pid : PeerId) : Driver.StateHistorySafe Safe (CausalJournal.session pid) :=
  receipt_quiet _ (old_state _) _ (fun _ => rfl)

private theorem selected (d : Device) (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    Driver.ProductHistorySafe Safe (hooks.timerSelected d j pid timer entry) := by
  intro w h hi
  exact Driver.History.product_bind
    (product_emit (.old (.timerSelected ⟨d,j,pid,timer,entry,w⟩)) rfl)
    (fun _ => product_enter (.timer j pid timer entry) (fun _ => rfl)) w h hi

private def neutral : Driver.Hooks Event := {hooks with stackInput := fun _ body => body}

private theorem ordinary : Driver.HooksHistorySafe Safe neutral where
  stagedPurge := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  peerRelease := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  deliver := by
    change Driver.ProductHistorySafe Safe (DeliverySource.observed Event.delivery)
    unfold DeliverySource.observed
    exact Driver.History.product_bind (Driver.History.product_lift _) (fun w =>
      Driver.History.product_bind (product_emit (.delivery w.sent) rfl) (fun _ =>
        Driver.History.product_lift _))
  keepalivePrepare := fun _ => receipt_quiet _ (Driver.History.state_lift _) _ (fun _ => rfl)
  fixtureEnter := fun trigger => state_enter (.fixture trigger) (fun _ => rfl)
  fixtureLeave := state_leave
  handshake := handshake
  sendWorker := send_worker
  flushedSend := flushed_send
  armTimer := effects_safe.arm
  queueSend := effects_safe.append
  candidateEnter := fun skb packet => product_enter (.candidate skb packet) (fun _ => rfl)
  candidateLeave := product_leave
  stackInput := fun _ _ preserves => preserves
  prepare := old_product _
  counterCheck := fun _ _ => old_product _
  timerSelected := selected
  timerFinished := product_leave
  selection := fun _ => old_state _
  confirmation := fun _ _ => old_state _
  session := session
  reserve := fun _ => old_state _
  allocate := fun _ => old_state _
  create := fun _ _ => old_state _
  front := fun _ _ _ _ => old_state _
  poll := old_product _
  encrypt := fun _ => old_product _
  transmit := transmit

theorem core : Driver.ActorCoreHistorySafe Safe hooks where
  stagedPurge := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  peerRelease := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  deliver := by
    change Driver.ProductHistorySafe Safe (DeliverySource.observed Event.delivery)
    unfold DeliverySource.observed
    exact Driver.History.product_bind (Driver.History.product_lift _) (fun w =>
      Driver.History.product_bind (product_emit (.delivery w.sent) rfl) (fun _ =>
        Driver.History.product_lift _))
  keepalivePrepare := fun _ => receipt_quiet _ (Driver.History.state_lift _) _ (fun _ => rfl)
  staging := Driver.staging_history (g := neutral) ordinary
  fixtureEnter := ordinary.fixtureEnter
  fixtureLeave := ordinary.fixtureLeave
  handshake := ordinary.core.handshake
  sendWorker := ordinary.sendWorker
  flushedSend := ordinary.flushedSend
  armTimer := ordinary.armTimer
  queueSend := ordinary.queueSend
  candidateEnter := ordinary.candidateEnter
  candidateLeave := ordinary.candidateLeave
  prepare := ordinary.prepare
  counterCheck := ordinary.counterCheck
  timerSelected := ordinary.timerSelected
  timerFinished := ordinary.timerFinished
  confirmation := ordinary.confirmation
  session := ordinary.session
  front := ordinary.front
  poll := ordinary.poll
  encrypt := ordinary.encrypt
  transmit := ordinary.transmit

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.StackOrigins
