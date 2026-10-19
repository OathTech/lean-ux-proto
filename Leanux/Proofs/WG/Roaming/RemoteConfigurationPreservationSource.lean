import Leanux.Proofs.WG.Roaming.RemoteConfigurationInvariantSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration RemoteSilent
open RemoteDriver

theorem lift_frame (entry : RemoteMap) {α : Type} (action : WG.M α)
    (frame : SameView destinationAt action) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (liftWGPrefix action) :=
  native_lift_retained entry action (fun before=>of_frame before action frame)

theorem access_frame (entry : RemoteMap) {α : Type} (observed : MixedM α) (action : WG.M α)
    (erase : ErasesStatePrefix observed action) (frame : SameView destinationAt action) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (access RemoteDriver.Event.rx rxEvent observed) :=
  access_retained entry observed action erase (fun before=>of_frame before action frame)

theorem out_covered (entry : RemoteMap) (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (access RemoteDriver.Event.rx rxEvent (peerConfigOutPrefix attrs peer ret)) := by
  apply access_retained entry _ (do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
  · exact erasesStatePrefix_bind (peerPutMixed_erases peer) (fun _ =>
      erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _=>erasesStatePrefix_pure _))
  · exact fun before=>out_retained before attrs peer ret

theorem invariant_contracts (entry : RemoteMap) :
    Invariant.Contracts (RemoteDriver.NativeInv entry) :=
  ⟨native_safe entry,native_lift_retained entry,access_retained entry,
    endpoint_covered entry,birth_covered entry⟩

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
