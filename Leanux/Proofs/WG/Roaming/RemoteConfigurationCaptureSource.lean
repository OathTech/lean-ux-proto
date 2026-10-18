import Leanux.Proofs.WG.Roaming.RemoteConfigurationBridge
import Leanux.Proofs.WG.Queues.JointDevice
import Leanux.Proofs.WG.Queues.TxDispositionProjection

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration

variable {E F α : Type}

theorem receipt_projects (decode : E → Option F)
    (a : WGPrefix E α) (old : WGPrefix F α)
    (receipt : WGRunWitness α → E)
    (projects : StateProjectsPrefix decode id a old)
    (ignored : ∀ r, decode (receipt r) = none) :
    StateProjectsPrefix decode id (receiptWGObserved a receipt) old := by
  intro w ambient h
  have original := projects w ambient h
  change runWGPrefix old w ambient (h.filterMap decode) =
    ((runWGPrefix a w ambient h).1.map (fun ((x,v),b) => ((x,v),b)),
      (runWGPrefix a w ambient h).2.filterMap decode) at original
  change runWGPrefix old w ambient (h.filterMap decode) =
    ((runWGPrefix (receiptWGObserved a receipt) w ambient h).1.map (fun ((x,v),b) => ((x,v),b)),
      (runWGPrefix (receiptWGObserved a receipt) w ambient h).2.filterMap decode)
  rw [runWGPrefix_receiptWGObserved]
  cases run : runWGPrefix a w ambient h with
  | mk result hist =>
    rw [run] at original
    cases result with
    | error stop => exact original
    | ok out =>
      rcases out with ⟨⟨value,final⟩,after⟩
      simpa only [List.filterMap_append,List.filterMap_cons,ignored,
        List.filterMap_nil,List.append_nil] using original

variable (encode : RxHistory.Event → E) (decode : E → Option RxHistory.Event)

def access (a : MixedM α) : WGPrefix E α :=
  focusStatePrefix encode decode (RoutingJoint.nativeRx a)

theorem access_projects (law : ∀ e, decode (encode e) = some e) (a : MixedM α) :
    StateProjectsPrefix decode id (access encode decode a) (RoutingJoint.nativeRx a) :=
  fun w => (StateAppends.focus _ _ _ w).project_focus encode decode law

theorem access_erases (a : MixedM α) (original : WG.M α)
    (erase : ErasesStatePrefix a original) :
    ErasesStatePrefix (access encode decode a) original :=
  focusStatePrefix_erases _ _ (focusStatePrefix_erases _ _
    (focusStatePrefix_erases _ _ erase))

def endpointObserved (emit : EndpointRun → E) (pid : PeerId) (endpoint : Endpoint) :
    WGPrefix E Unit :=
  receiptWGObserved (access encode decode (setPeerEndpointPrefix pid endpoint))
    (fun run => emit ⟨pid,endpoint,run⟩)

def birthObserved (emit : PeerCreateReceipt → E) (key : Key) (psk : Option Key) :
    WGPrefix E (Except Int PeerId) :=
  receiptWGObserved (access encode decode (peerCreateMixed key psk))
    (fun run => emit (birthReceipt key psk run))

theorem endpointObserved_projects (law : ∀ e, decode (encode e) = some e)
    (emit : EndpointRun → E) (ignored : ∀ r, decode (emit r) = none)
    (pid : PeerId) (endpoint : Endpoint) :
    StateProjectsPrefix decode id (endpointObserved encode decode emit pid endpoint)
      (RoutingJoint.nativeRx (setPeerEndpointPrefix pid endpoint)) :=
  receipt_projects decode _ _ _ (access_projects encode decode law _) (fun _ => ignored _)

theorem birthObserved_projects (law : ∀ e, decode (encode e) = some e)
    (emit : PeerCreateReceipt → E) (ignored : ∀ r, decode (emit r) = none)
    (key : Key) (psk : Option Key) :
    StateProjectsPrefix decode id (birthObserved encode decode emit key psk)
      (RoutingJoint.nativeRx (peerCreateMixed key psk)) :=
  receipt_projects decode _ _ _ (access_projects encode decode law _) (fun _ => ignored _)

theorem endpointObserved_erases (emit : EndpointRun → E) (pid : PeerId) (endpoint : Endpoint) :
    ErasesStatePrefix (endpointObserved encode decode emit pid endpoint) (setPeerEndpoint pid endpoint) :=
  receiptWGObserved_erases (access_erases encode decode _ _ (setPeerEndpointPrefix_erases pid endpoint)) _

theorem birthObserved_erases (emit : PeerCreateReceipt → E) (key : Key) (psk : Option Key) :
    ErasesStatePrefix (birthObserved encode decode emit key psk) (peerCreate key psk) :=
  receiptWGObserved_erases (access_erases encode decode _ _ (peerCreateMixed_erases key psk)) _

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
