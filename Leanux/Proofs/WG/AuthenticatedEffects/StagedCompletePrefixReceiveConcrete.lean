import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixReceivePollSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixTransmit
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixTimerCallbacks

/-! All true staging, transmit and keepalive callbacks are discharged by their
actual prefix source proofs. These contracts concern logical journal prefixes
beside full native endpoint carriers, not a silent-interval correspondence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity RetirementSecurity CausalJournal ReceivePoll
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

theorem safe (h : List Event) (w : World)
    (before : With (Carrier debts locals) CompleteProduct.Safe h w) : All CompleteProduct.Safe h := before.2

theorem consume (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint) :
    Passive.Checked debts locals CompleteProduct.Safe (Driver.consumeObserved hooks pid packet endpoint) :=
  ReceiveConsumer.checked CompleteProduct.Safe Transmit.account pid packet endpoint (Staging.staging debts locals pid)

theorem stack (bytes : List UInt8) : Checked debts locals CompleteProduct.Safe (Driver.stackObserved hooks bytes) :=
  ReceiveStack.stack CompleteProduct.Safe Transmit.transmit bytes

theorem native_poll (pid : PeerId) (budget : Nat) : Checked debts locals CompleteProduct.Safe
    (Driver.nativePollObserved hooks pid budget) :=
  ReceivePollSource.native_poll CompleteProduct.Safe Transmit.account
    (Staging.staging debts locals) Transmit.transmit pid budget

theorem timer (pid : PeerId) (timer : PeerTimer) : Passive.Checked debts locals CompleteProduct.Safe
    (Driver.timerObserved hooks pid timer) :=
  TimerCallbacks.callback CompleteProduct.Safe Transmit.account pid timer (Transmit.keepalive pid)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveConcrete
