import Leanux.Proofs.WG.Noise.PendingSchedulerSource
import Leanux.Proofs.WG.Noise.PendingCryptSource
import Leanux.Proofs.WG.Noise.PendingStackSource
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTraffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PendingSession

theorem index_native (kinds : List IndexKind) (index : Nat) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (indexLookup kinds index) :=
  PendingReception.native_preserves _ (ConfiguredIdentity.indexLookup_preserves kinds index)
    (CurrentSlots.indexLookup_preserves kinds index)
    (PendingTickets.retained_of_frame (PendingReception.indexLookup_pending_frame kinds index)) seen

theorem acquire_native (kid : Option KeypairId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (keypairGet kid) :=
  PendingReception.native_preserves _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredTraffic.«0».Leanux.Proofs.WG.ConfiguredTraffic.keyGet) kid)
    (CurrentSlots.keypairGet_preserves kid)
    (PendingTickets.retained_of_staging_ordinary _ (Index.keypairGet_staging kid)
      (Keypairs.SameView.ordinary (Keypairs.keypairGet_sameSnapshot kid))) seen

theorem enqueue_native (id : SkbId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (enqueuePerDeviceAndPeerRx id) :=
  PendingReception.native_view _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.enqueuePerDeviceAndPeerRx_view) id)
    (CurrentSlots.fields_preserves (project := fun w => w) (CurrentSlots.enqueuePerDeviceAndPeerRx_fields id))
    (PendingTickets.frame_from_fields (CurrentSlots.enqueuePerDeviceAndPeerRx_fields id)
      (Keypairs.WGMore.enqueuePerDeviceAndPeerRx_sameSnapshot id)) seen

theorem multicast_store (family addr : Nat) :
    SameProductStore (Env.xmitMulticastLoop family addr) := by
  unfold Env.xmitMulticastLoop
  split
  · exact liftWG_sameProductStore _ (loopbackSend_kernel [] true)
  · split
    · exact fun _ => productAmbient_spec _ _ (fun _ _ hi => hi)
    · exact SameView.pure _ _

end Leanux.Proofs.WG.Noise.PendingTraffic
