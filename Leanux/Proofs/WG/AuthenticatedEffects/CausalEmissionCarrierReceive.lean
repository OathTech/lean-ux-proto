import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionNapi
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionTimers

/-! Receive, stack and timer actors preserve both live append accounting and
all earlier delivery certificates on the same native execution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem device_transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved hooks family addr packets mtu) :=
  state_combine _ (Emissions.device_transmit family addr packets mtu)
    (Driver.transmit_history (g := quietHooks) quiet_hooks.core family addr packets mtu)

theorem stack (bytes : List UInt8) : ProductSafe (Driver.stackObserved hooks bytes) :=
  product_combine _ (Emissions.stack bytes) (Driver.stack_history (g := quietHooks) quiet_hooks.core bytes)

theorem native_poll (pid : PeerId) (budget : Nat) : ProductSafe (Driver.nativePollObserved hooks pid budget) :=
  product_combine _ (Emissions.native_poll pid budget) (native_poll_history pid budget)

theorem softirq : ProductSafe (Driver.softirqObserved hooks) :=
  product_combine _ Emissions.softirq (Driver.softirq_history (g := quietHooks) quiet_hooks.actors)

theorem inline_poll : ProductSafe (Driver.inlinePollObserved hooks) :=
  product_combine _ Emissions.inline_poll (Driver.inline_history (g := quietHooks) quiet_hooks.actors)

theorem irq_exit : ProductSafe (Driver.irqExitObserved hooks) :=
  product_combine _ Emissions.irq_exit (Driver.irqExit_history (g := quietHooks) quiet_hooks.actors)

theorem timer (pid : PeerId) (kind : PeerTimer) : StateSafe (Driver.timerObserved hooks pid kind) := by
  apply state_combine _ _ (Driver.timer_history (g := quietHooks) quiet_hooks.core pid kind)
  cases kind
  · exact Emissions.retransmit pid
  · exact Emissions.expired_keepalive _ Emissions.keepalive pid
  · exact Emissions.expired_new pid
  · exact Emissions.expired_zero pid
  · exact Emissions.persistent _ Emissions.keepalive pid

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
