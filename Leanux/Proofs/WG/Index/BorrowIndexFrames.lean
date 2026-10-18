import Leanux.Proofs.WG.Index.ConfigurationIndexFrames
import Leanux.Proofs.WG.Queues.RxBorrow
set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes

def borrowIndexFields (s : WGStoreView × (PeerId → Option Peer)) : Option (Nat × SenderDeviceCell) :=
  s.1.dev.map fun d => (d.nextKeypairId,
    (d.indexTable,d.ifindex,fun kid => d.keypairs[kid]?,
      fun pid => (s.2 pid).map senderPeerCell))

theorem borrowIndexFields_factor (w : WGWorld) :
    ConfigurationIndex.fields w = borrowIndexFields (PeerBorrow.view w) := by
  cases device : w.dev <;>
    simp [ConfigurationIndex.fields,ConfigurationIndex.deviceFields,borrowIndexFields,
      PeerBorrow.view,PeerBorrow.outsidePeers,PeerBorrow.resident,wgStoreView,
      senderDeviceCell,device]

theorem lookupRepay_indexFields (protocol : Nat) (bytes : List UInt8) :
    SameView ConfigurationIndex.fields (Queues.RxBorrow.source protocol bytes) :=
  (Queues.RxBorrow.source_frame protocol bytes).of_factor
    borrowIndexFields ConfigurationIndex.fields borrowIndexFields_factor
end Leanux.Proofs.WG.Index
