import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryDeviceConfiguration
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTransmitSource

/-! Concrete configuration and opening contracts discharge all staging and
keepalive callbacks. The local allocation companion remains explicit until
initialized runner transport; no fresh-peer hypothesis is assumed per call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationClosed
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal AllocatedCarrier

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

theorem peer (attrs : PeerAttrs) :
    Checked debts locals (Transmit.Accounted debts locals) (Driver.configPeer hooks attrs) :=
  ConfigurationReady.peer _ (fun ledger h w entry => .entry ledger h w entry)
    Transmit.staging Transmit.keepalive attrs

theorem device (attrs : DeviceAttrs) :
    Checked debts locals (Transmit.Accounted debts locals) (Driver.configDevice hooks attrs) :=
  DeviceConfiguration.device _ (fun ledger h w entry => .entry ledger h w entry)
    Transmit.staging Transmit.keepalive attrs

theorem opened :
    Checked debts locals (Transmit.Accounted debts locals) (Driver.openObserved hooks) :=
  pair _ (ConfigurationTail.opened _ (fun ledger h w entry => .entry ledger h w entry)
    Transmit.staging Transmit.keepalive) ConfigurationNative.open_erases
    (AllocatedFrames.observed (DeviceControlCall.erases .openDevice) (DeviceControlCall.allocation .openDevice))

theorem up : Checked debts locals (Transmit.Accounted debts locals) (Driver.upObserved hooks) :=
  pair _ (ConfigurationTail.up _ (fun ledger h w entry => .entry ledger h w entry)
    Transmit.staging Transmit.keepalive) ConfigurationNative.up_erases
    (AllocatedFrames.observed (DeviceControlCall.erases .up) (DeviceControlCall.allocation .up))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationClosed
