import Leanux.Proofs.WG.Index.ReceiveCompletionSource
import Leanux.Proofs.WG.Index.BorrowIndexFrames
import Leanux.Proofs.WG.Index.ConfigurationEndpointFrames
import Leanux.Proofs.WG.Index.IncomingCallerFrames
import Leanux.Proofs.WG.Index.ConfirmationIndexClaims
import Leanux.Proofs.WG.Index.TimerCoreSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReceiveCompletion
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues

theorem store_fields {α : Type} {action : WG.M α} (same : SameWGStore action) :
    SameView ConfigurationIndex.fields action :=
  same.of_factor (fun s : WGStoreView => s.dev.map ConfigurationIndex.deviceFields)
    ConfigurationIndex.fields (fun _=>rfl)

theorem stats_fields (pid : PeerId) (len : Nat) :
    SameView ConfigurationIndex.fields (updateRxStats pid len) := by
  change SameView ConfigurationIndex.fields
    ((modifyDev fun d=>{d with rxPackets:=d.rxPackets+1,rxBytes:=d.rxBytes+len}) >>=
      fun _=>modifyPeer pid fun p=>{p with rxBytes:=p.rxBytes+len})
  exact (ConfigurationIndex.modifyDev_fields
    (fun d : Device=>{d with rxPackets:=d.rxPackets+1,rxBytes:=d.rxBytes+len}) (fun _=>rfl)).bind
    (fun _=>ConfigurationIndex.modifyPeer_fields pid (fun p=>{p with rxBytes:=p.rxBytes+len}) (fun _=>rfl))

theorem dishonest_fields (why : Dishonest) :
    SameView ConfigurationIndex.fields (WG.dishonest why) :=
  ConfigurationIndex.modifyDev_fields _ (fun d=>by cases why <;> rfl)

def borrowSlots (s : WGStoreView × (PeerId → Option Peer)) :=
  (s.1.dev.map (·.nextKeypairId),fun pid=>(s.2 pid).map CurrentSlots.slotCell,
    fun kid : KeypairId=>(s.1.dev.bind fun d=>d.keypairs[kid]?).map (·.peer))

theorem borrowSlots_factor (w : WGWorld) :
    CurrentSlots.fields w=borrowSlots (PeerBorrow.view w) := by
  unfold CurrentSlots.fields borrowSlots Leanux.Proofs.WG.Queues.RxCredits.keyWords
  cases device:w.dev <;>
    simp [PeerBorrow.view,PeerBorrow.outsidePeers,PeerBorrow.resident,wgStoreView,device]

theorem lookupRepay_slots (protocol : Nat) (bytes : List UInt8) :
    Preserves CurrentSlots.Inv (RxBorrow.source protocol bytes) :=
  CurrentSlots.fields_preserves (project:=id)
    ((RxBorrow.source_frame protocol bytes).of_factor borrowSlots
      CurrentSlots.fields borrowSlots_factor)

theorem store_slots {α : Type} {action : WG.M α} (same : SameWGStore action) :
    Preserves CurrentSlots.Inv action :=
  CurrentSlots.fields_preserves (project:=id)
    (same.of_factor (fun s : WGStoreView=>CurrentSlots.fields {dev:=s.dev})
      CurrentSlots.fields (fun _=>rfl))


end Leanux.Proofs.WG.Index.ReceiveCompletion
