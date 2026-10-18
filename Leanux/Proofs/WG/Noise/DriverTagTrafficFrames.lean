import Leanux.Proofs.WG.Noise.DriverTagSilentSource
import Leanux.Proofs.WG.Noise.DriverTagProductSource
import Leanux.Proofs.WG.Noise.DriverTagTransmitSource
import Leanux.Proofs.WG.Queues.RxIngressCarrier
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation
import Leanux.Proofs.WG.Noise.DriverTagScheduledSource
import Leanux.Proofs.WG.Noise.PendingTrafficFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Traffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

theorem index_frame (kinds : List IndexKind) (index : Nat) :
    SameView tagView (indexLookup kinds index) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient value final after run
  exact (indexLookup_spec_responseTagMap_variant kinds index g.dev
    g ambient value final after rfl run).1

theorem enqueue_frame (id : SkbId) : SameView tagView (enqueuePerDeviceAndPeerRx id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient value final after run
  have startRun := run
  simp only [enqueuePerDeviceAndPeerRx,MaterialOrigin.bind_ok_ambient] at startRun
  obtain ⟨u,a,aa,hset,pkt,b,ab,hread,p,c,ac,hpeer,rest⟩ := startRun
  cases device : g.dev with
  | none =>
    simp [setRxSkb,SkbStore.setRx,liftSkb_run,SkbStore.getRx,device,
      invariant,AmbientM.invariant] at hset
  | some d =>
    cases packet : d.rxSkbs[id]? with
    | none =>
      simp [setRxSkb,SkbStore.setRx,liftSkb_run,SkbStore.getRx,device,packet,
        invariant,AmbientM.invariant] at hset
      cases hset
    | some original =>
      rw [Packets.setRxSkb_run g ambient d id original _ device packet] at hset
      cases hset
      obtain ⟨rfl,rfl,readDev,readDevice,readPacket⟩ :=
        Packets.getRxSkb_current id _ b pkt ambient ab hread
      have deviceRead : readDev = {d with rxSkbs := d.rxSkbs.insert id {original with state := .uncrypted}} := by
        simpa [Packets.update,device] using readDevice.symm
      subst readDev
      have packetRead : pkt = {original with state := .uncrypted} := by simpa using readPacket.symm
      subst pkt
      obtain ⟨_,_,peerDev,peerDevice,resident⟩ := getPeer_normal original.peer _ c p _ ac hpeer
      have devicePeer : peerDev = {d with rxSkbs := d.rxSkbs.insert id {original with state := .uncrypted}} := by
        simpa [Packets.update,device] using peerDevice.symm
      subst peerDev
      obtain ⟨_,cpu,effect⟩ := RxCredits.enqueue_effect device packet resident _ after run
      have ending := congrArg WGStoreView.dev effect
      change final.dev = some _ at ending
      change responseTagMap final.dev = responseTagMap g.dev
      rw [ending,device]
      unfold RxCredits.enqueueDevice
      split
      · rfl
      · exact tagMap_write d original.peer p _ resident rfl

end Leanux.Proofs.WG.Noise.DriverTags.Traffic
