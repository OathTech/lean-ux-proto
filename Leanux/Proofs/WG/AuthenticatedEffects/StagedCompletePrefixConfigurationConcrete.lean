import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixConfigurationDevice
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixTransmit
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteNativeCalls
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixSendDrain

/-! Concrete staging and keepalive discharge all admission callbacks in
configuration and opening. The actual bounded send/clear drain uses its separate prefix source proof. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal
open ConfigurationAllocated (Checked)
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

theorem peer (attrs : PeerAttrs) : Checked debts locals CompleteProduct.Safe (Driver.configPeer hooks attrs) :=
  ConfigurationReady.peer CompleteProduct.Safe Transmit.account (Staging.staging debts locals)
    Transmit.keepalive (SendDrain.checked CompleteProduct.Safe Transmit.account) attrs

theorem device (attrs : DeviceAttrs) : Checked debts locals CompleteProduct.Safe (Driver.configDevice hooks attrs) :=
  ConfigurationDevice.device CompleteProduct.Safe Transmit.account (SendDrain.checked CompleteProduct.Safe Transmit.account)
    (Staging.staging debts locals) Transmit.keepalive attrs

theorem opened : Checked debts locals CompleteProduct.Safe (Driver.openObserved hooks) :=
  ConfigurationAllocated.pair CompleteProduct.Safe
    (ConfigurationTail.opened CompleteProduct.Safe Transmit.account (Staging.staging debts locals) Transmit.keepalive)
    ConfigurationNative.open_erases
    (AllocatedFrames.observed (DeviceControlCall.erases .openDevice) (DeviceControlCall.allocation .openDevice))

theorem up : Checked debts locals CompleteProduct.Safe (Driver.upObserved hooks) :=
  ConfigurationAllocated.pair CompleteProduct.Safe
    (ConfigurationTail.up CompleteProduct.Safe Transmit.account (Staging.staging debts locals) Transmit.keepalive)
    ConfigurationNative.up_erases
    (AllocatedFrames.observed (DeviceControlCall.erases .up) (DeviceControlCall.allocation .up))

theorem remove (peer : Option PeerId) : Checked debts locals CompleteProduct.Safe (Driver.removeObserved hooks peer) :=
  ConfigurationDevice.remove CompleteProduct.Safe Transmit.account (SendDrain.checked CompleteProduct.Safe Transmit.account) peer

theorem remove_all : Checked debts locals CompleteProduct.Safe (Driver.removeAllObserved hooks) :=
  ConfigurationDevice.remove_all CompleteProduct.Safe Transmit.account (SendDrain.checked CompleteProduct.Safe Transmit.account)

theorem down : Checked debts locals CompleteProduct.Safe (Driver.downObserved hooks) :=
  ConfigurationAllocated.pair CompleteProduct.Safe
    (Lifecycle.down CompleteProduct.Safe Transmit.account (SendDrain.checked CompleteProduct.Safe Transmit.account)) CompleteNative.down_erases CompleteNative.down

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationConcrete
