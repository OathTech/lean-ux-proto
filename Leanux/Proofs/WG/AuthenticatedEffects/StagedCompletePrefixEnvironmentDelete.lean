import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixLifecyclePacket
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketEnvironmentChecked

/-! Actual environment deletion retains all journal prefixes. Native guard,
shutdown and reset prerequisites follow the same source cuts as the existing
endpoint theorem; no endpoint-only reconstruction of prefixes is used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.EnvironmentDelete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits TransmitSecurity RetirementSecurity CausalJournal
variable (drained : ∀ upTo, Passive.Checked [] [] CompleteProduct.Safe (Driver.sendDrainObserved hooks upTo))

theorem quiet (action : Leanux.M α) (frame : SameProductStore action) :
    Ensures RetiredPeer.Lifecycle.Packet.Environment.Ready CompleteProduct.Safe (liftPrefix action) (fun _=>RetiredPeer.Lifecycle.Packet.Environment.Ready) :=
  Ensures.quiet (RetiredPeer.Lifecycle.Packet.Environment.quiet action frame) (fun _ _=>rfl)

include drained in
theorem down : Ensures RetiredPeer.Lifecycle.Packet.Environment.Ready CompleteProduct.Safe
    (liftWGObserver (Driver.downObserved hooks)) (fun _=>RetiredPeer.Lifecycle.Packet.Environment.Ready) :=
  Ensures.join
    ((ConfigurationAllocated.pair CompleteProduct.Safe
      (Lifecycle.down CompleteProduct.Safe Transmit.account drained)
      CompleteNative.down_erases CompleteNative.down).liftWG)
    RetiredPeer.Lifecycle.Packet.Environment.down_checked (fun _ _ before=>before.1)

include drained in
theorem notification_prefix : Ensures RetiredPeer.Lifecycle.Packet.Environment.Ready CompleteProduct.Safe RetiredPeer.Lifecycle.Packet.Environment.prefixObserved
    (fun _=>RetiredPeer.Lifecycle.Packet.Environment.Ready) := by
  have read := quiet (liftWG getDev) (liftWG_sameProductStore _ getDev_sameWGStore)
  have cut := quiet (skipCut allocCuts) (fun initial=>productAmbient_spec _ (fun w=>productStoreView w=initial) (fun _ _ before=>before))
  have sleep := quiet (liftWG mayHaveSlept) (liftWG_sameProductStore _ mayHaveSlept_sameWGStore)
  unfold RetiredPeer.Lifecycle.Packet.Environment.prefixObserved
  apply Ensures.bind read
  intro d
  split
  · exact Ensures.bind (down drained) (fun _=>
      Ensures.bind (quiet _ RetiredPeer.Lifecycle.Packet.Environment.notify_down_store) (fun _=>
        Ensures.bind cut (fun _=>Ensures.bind (quiet _ RetiredPeer.Lifecycle.Packet.Environment.notify_unregister_store) (fun _=>sleep))))
  · exact Ensures.bind cut (fun _=>Ensures.bind (quiet _ RetiredPeer.Lifecycle.Packet.Environment.notify_unregister_store) (fun _=>sleep))

theorem guards : Ensures (RetiredPeer.Lifecycle.Packet.Environment.Entry cs) CompleteProduct.Safe
    (liftPrefix HolderDeviceDelete.guards) (fun _=>RetiredPeer.Lifecycle.Packet.Environment.Ready) :=
  Ensures.quiet RetiredPeer.Lifecycle.Packet.Environment.guards_checked (fun _ _=>rfl)

include drained in
/-- The real guard discharges the receive carrier before actual shutdown and
destruction. Its independent exact-account/positive/service premises remain
visible; there is no incoming idle or staged-empty assumption. -/
theorem checked : Ensures (RetiredPeer.Lifecycle.Packet.Environment.Entry cs) CompleteProduct.Safe
    (Driver.envDeleteObserved hooks) (fun _=>CompleteProduct.Carrier) := by
  rw [RetiredPeer.Lifecycle.Packet.Environment.source_factor]
  apply Ensures.bind guards
  intro _
  apply Ensures.bind (Q:=fun (_ : WGWorld)=>RetiredPeer.Lifecycle.Packet.Environment.Ready) (quiet getWG (fun initial=>productGetWG_spec (·=initial)))
  intro w
  split
  · exact Ensures.pure (-ENODEV) (fun _ _ before=>before.1)
  · apply Ensures.bind (Q:=fun (_ : Unit)=>RetiredPeer.Lifecycle.Packet.Environment.Ready) (notification_prefix drained)
    intro _
    exact Ensures.bind (LifecyclePacket.checked drained).liftWG
      (fun _=>Ensures.pure 0 (fun _ _ before=>before))

/-- Concrete deletion retains the actual exact-account, physical, positive
and service boundary required by the guarded native destructor. -/
theorem concrete : Ensures (RetiredPeer.Lifecycle.Packet.Environment.Entry cs) CompleteProduct.Safe
    (Driver.envDeleteObserved hooks) (fun _=>CompleteProduct.Carrier) :=
  checked (SendDrain.checked CompleteProduct.Safe Transmit.account)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.EnvironmentDelete
