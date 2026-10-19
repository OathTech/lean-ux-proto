import Leanux.Proofs.WG.Roaming.RemoteChronologyBridge
import Leanux.Proofs.WG.Roaming.RemoteChronologyJournalSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged

def NativeInv (entry : RemoteMap) (history : List RemoteDriver.Event) (g : WGWorld) : Prop :=
  RemoteChronology.Inv effect entry RemoteDriver.EventValid history (destinationAt g)

def Inv (entry : RemoteMap) (history : List RemoteDriver.Event) (w : World) : Prop :=
  NativeInv entry history w.wg

theorem endpoint_preserves (entry : RemoteMap) (pid : PeerId) (endpoint : Endpoint) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) RemoteDriver.Safe
      (RemoteDriver.endpointObserved pid endpoint) := by
  apply native_focused_receipt_inert effect entry RemoteDriver.EventValid
    RemoteDriver.Event.rx RemoteDriver.rxEvent (fun _ => True.intro) destinationAt
    (RoutingJoint.nativeRx (setPeerEndpointPrefix pid endpoint)) (setPeerEndpoint pid endpoint)
    (nativeRx_history_inert (fun event pid => effect (.rx event) pid) (fun _ _ => rfl) _)
    (StateAppends.focus _ _ _)
    (focusStatePrefix_erases _ _ (focusStatePrefix_erases _ _ (setPeerEndpointPrefix_erases pid endpoint)))
    (fun r => .endpoint ⟨pid,endpoint,r⟩) (fun _ run => run)
  exact fun r valid => endpoint_effect ⟨pid,endpoint,r⟩ valid

theorem birth_preserves (entry : RemoteMap) (key : Key) (psk : Option Key) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) RemoteDriver.Safe
      (RemoteDriver.birthObserved key psk) := by
  apply native_focused_receipt_inert effect entry RemoteDriver.EventValid
    RemoteDriver.Event.rx RemoteDriver.rxEvent (fun _ => True.intro) destinationAt
    (RoutingJoint.nativeRx (peerCreateMixed key psk)) (peerCreate key psk)
    (nativeRx_history_inert (fun event pid => effect (.rx event) pid) (fun _ _ => rfl) _)
    (StateAppends.focus _ _ _)
    (focusStatePrefix_erases _ _ (focusStatePrefix_erases _ _ (peerCreateMixed_erases key psk)))
    (fun r => .birth (RemoteConfiguration.birthReceipt key psk r))
    (fun r run => RemoteConfiguration.birthReceipt_valid key psk r run)
  exact fun r valid => birth_effect (RemoteConfiguration.birthReceipt key psk r)
    (RemoteConfiguration.birthReceipt_valid key psk r valid)

theorem receive_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.receiveStepObserved := by
  apply focused_receipt_inert effect entry RemoteDriver.EventValid
    RemoteDriver.Event.rx RemoteDriver.rxEvent (fun _ => True.intro)
    (fun w : World => destinationAt w.wg) (fun (_ : Bool) w => destinationAt w.wg)
    Origins.HistoryAdapters.receiveStep (liftWG receiveStep)
    (historyFocus_history_inert (fun event pid => effect (.rx event) pid)
      (by intro event pid; cases event <;> rfl) _)
    (Appends.focus _ _ _) Origins.HistoryAdapters.receiveStep_erases
    RemoteDriver.Event.receive (fun _ run => run)
  exact receive_effect

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
