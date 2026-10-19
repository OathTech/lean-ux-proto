import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeviceConfiguration
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct

/-! Concrete configuration discharges its paired transmit callbacks. The
native allocation companion derives freshness; stopped selected packets keep
their actual source anchors through CompleteTransmit.Safe. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem config_peer (attrs : PeerAttrs) : StateChecked (Driver.configPeer hooks attrs) :=
  CompleteConfigurationReady.peer Safe account_safe (fun pid => source_state (CompleteTransmit.staging pid))
    (fun pid => source_state (CompleteTransmit.keepalive pid)) attrs

theorem config_device (attrs : DeviceAttrs) : StateChecked (Driver.configDevice hooks attrs) :=
  CompleteDeviceConfiguration.device Safe account_safe (fun pid => source_state (CompleteTransmit.staging pid))
    (fun pid => source_state (CompleteTransmit.keepalive pid)) attrs

theorem opened : StateChecked (Driver.openObserved hooks) :=
  pair (CompleteConfigurationTail.opened Safe account_safe (fun pid => source_state (CompleteTransmit.staging pid))
    (fun pid => source_state (CompleteTransmit.keepalive pid)))
    ConfigurationNative.open_erases
    (AllocatedFrames.observed (DeviceControlCall.erases .openDevice) (DeviceControlCall.allocation .openDevice))

theorem up : StateChecked (Driver.upObserved hooks) :=
  pair (CompleteConfigurationTail.up Safe account_safe (fun pid => source_state (CompleteTransmit.staging pid))
    (fun pid => source_state (CompleteTransmit.keepalive pid)))
    ConfigurationNative.up_erases
    (AllocatedFrames.observed (DeviceControlCall.erases .up) (DeviceControlCall.allocation .up))

theorem remove (peer : Option PeerId) : StateChecked (Driver.removeObserved hooks peer) :=
  pair (CompleteLifecycle.remove Safe account_safe peer) (ConfigurationNative.remove_erases peer)
    (ConfigurationNative.removal peer)

theorem remove_all : StateChecked (Driver.removeAllObserved hooks) :=
  pair (CompleteLifecycle.remove_all Safe account_safe) ConfigurationNative.remove_all_erases
    ConfigurationNative.removal_all

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
