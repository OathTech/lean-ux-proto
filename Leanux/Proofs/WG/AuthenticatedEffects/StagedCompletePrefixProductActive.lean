import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProductLeaves
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixHandshakeWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixReceiveNapi
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixScheduler

/-! Concrete worker contracts join the original native endpoint with every
logical journal prefix. All callbacks in these worker iterations are discharged
on their original bodies; native interval reachability remains separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal

theorem keepalive (pid : PeerId) : StateChecked (Driver.keepaliveObserved hooks pid) :=
  pair (Transmit.keepalive pid) (CompleteProduct.keepalive pid)

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateChecked (Driver.transmitObserved hooks family addr packets mtu) :=
  pair (Transmit.transmit family addr packets mtu) (CompleteProduct.transmit family addr packets mtu)

theorem handshake : StateChecked (Driver.handshakeObserved hooks) :=
  pair (HandshakeWorker.session_worker CompleteProduct.Safe CompleteProduct.account_safe
    (Driver.keepaliveObserved hooks) Transmit.keepalive) CompleteProduct.handshake

theorem softirq : Checked (Driver.softirqObserved hooks) :=
  pair_product ReceiveNapi.softirq CompleteProduct.softirq

theorem inline_poll : Checked (Driver.inlinePollObserved hooks) :=
  pair_product ReceiveNapi.inline_poll CompleteProduct.inline_poll

theorem irq_exit : Checked (Driver.irqExitObserved hooks) :=
  pair_product ReceiveNapi.irq_exit CompleteProduct.irq_exit

theorem timer (pid : PeerId) (timer : PeerTimer) : StateChecked (Driver.timerObserved hooks pid timer) :=
  pair (ReceiveConcrete.timer pid timer) (CompleteProduct.timer pid timer)

theorem encrypt_iteration : Checked (Driver.encryptIterObserved hooks) :=
  encrypt_iter poll softirq encrypt

theorem decrypt_iteration : Checked (Driver.decryptIterObserved hooks) :=
  decrypt_iter (decrypt_step prepare (fun pid => state (release (some pid))) softirq irq_exit)

theorem receive_iteration : Checked (Driver.receiveIterObserved hooks) := receive_iter (state handshake)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
