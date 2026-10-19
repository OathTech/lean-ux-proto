import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionQuietHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionQuietSend
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionQuietCompletion
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryReceive

/-! Independent history contracts for ordinary actors which never call the
delivery hook. The surrogate changes only that hook; actual delivery uses the
state-dependent pre-clear certificate, not this quiet contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
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

def quietHooks : Driver.Hooks Event := {hooks with deliver := liftPrefix Env.deliverSent}

theorem quiet_hooks : Driver.HooksHistorySafe Safe quietHooks where
  deliver := Driver.History.product_lift _
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
  stackInput := fun entry _ preserves => product_scope (.stackInput entry) (fun _ => rfl) _ (fun _ => preserves)
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

theorem staging_history (pid : PeerId) : Driver.StateHistorySafe Safe (Driver.stagingObserved hooks pid) :=
  Driver.staging_history (g := quietHooks) quiet_hooks pid

theorem keepalive_history (pid : PeerId) : Driver.StateHistorySafe Safe (Driver.keepaliveObserved hooks pid) :=
  Driver.keepalive_history (g := quietHooks) quiet_hooks pid

theorem handshake_history : Driver.StateHistorySafe Safe (Driver.handshakeObserved hooks) :=
  Driver.handshake_history (g := quietHooks) quiet_hooks.actors

theorem native_poll_history (pid : PeerId) (budget : Nat) :
    Driver.ProductHistorySafe Safe (Driver.nativePollObserved hooks pid budget) :=
  quiet_hooks.actors.nativePoll pid budget

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
