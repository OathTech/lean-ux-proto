import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionOld
import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionCompletion
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryWorkers
import Leanux.Proofs.WG.TransmitSecurity.DriverNeutralCalls

/-! Ordinary actor contracts reuse the common driver history proofs. The local
surrogate changes only the two selectors these actors do not call; actual work
and timer dispatch retain their separate guarded contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private def quietHooks : Driver.Hooks Event :=
  { hooks with flushedSend := fun pid => liftWGPrefix (runFlushedSendWork pid)
               timerSelected := fun _ _ _ _ _ => pure 0 }

private theorem quiet_hooks : Driver.HooksHistorySafe Safe quietHooks where
  fixtureEnter := fun trigger => state_enter (.fixture trigger) (fun _ => True.intro)
  fixtureLeave := state_leave
  handshake := handshake
  sendWorker := by
    rw [Driver.sendWorker_lift quietHooks rfl]
    exact Driver.History.product_lift _
  flushedSend := fun _ => Driver.History.state_lift _
  armTimer := effects_safe.arm
  queueSend := effects_safe.append
  candidateEnter := fun skb packet => product_enter (.candidate skb packet) (fun _ => True.intro)
  candidateLeave := product_leave
  stackInput := fun entry _ preserves => product_scope (.stackInput entry) (fun _ => True.intro) _ (fun _ => preserves)
  prepare := prepare
  counterCheck := counter
  timerSelected := fun _ _ _ _ _ => Driver.History.product_pure _
  timerFinished := product_leave
  selection := selection
  confirmation := confirmation
  session := session
  reserve := reserve
  allocate := allocate
  create := create
  front := front
  poll := poll
  encrypt := encrypt
  transmit := transmit

theorem staging_history (pid : PeerId) : Driver.StateHistorySafe Safe (Driver.stagingObserved hooks pid) :=
  Driver.staging_history (g := quietHooks) quiet_hooks pid

theorem keepalive_history (pid : PeerId) : Driver.StateHistorySafe Safe (Driver.keepaliveObserved hooks pid) :=
  Driver.keepalive_history (g := quietHooks) quiet_hooks pid

theorem handshake_history : Driver.StateHistorySafe Safe (Driver.handshakeObserved hooks) :=
  Driver.handshake_history (g := quietHooks) quiet_hooks.actors

theorem timer_history (pid : PeerId) (timer : PeerTimer) :
    Driver.StateHistorySafe Safe (Driver.timerObserved hooks pid timer) :=
  Driver.timer_history (g := quietHooks) quiet_hooks.core pid timer

theorem transmit_history (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (Driver.transmitObserved hooks family addr packets mtu) :=
  Driver.transmit_history (g := quietHooks) quiet_hooks.core family addr packets mtu

theorem softirq_history : Driver.ProductHistorySafe Safe (Driver.softirqObserved hooks) :=
  Driver.softirq_history (g := quietHooks) quiet_hooks.actors

theorem inline_history : Driver.ProductHistorySafe Safe (Driver.inlinePollObserved hooks) :=
  Driver.inline_history (g := quietHooks) quiet_hooks.actors

theorem iteration_history (activation : Activation) :
    Driver.ProductHistorySafe Safe (Driver.iterationObserved hooks activation) :=
  Driver.iteration_history (g := quietHooks) quiet_hooks.actors activation

theorem schedule_history (stack : Option Worker) :
    Driver.ProductHistorySafe Safe (Driver.scheduleObserved hooks stack) :=
  Driver.schedule_history (g := quietHooks) quiet_hooks.actors stack

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
