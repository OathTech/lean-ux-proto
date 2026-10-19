import Leanux.Proofs.WG.TimerDiscipline.SessionCounterFrames
import Leanux.Proofs.WG.Keypairs.Frames.WGMore
import Leanux.Proofs.WG.Keypairs.Frames.WGDevice
import Leanux.Proofs.WG.Keypairs.Frames.Env

/-! Counter monotonicity for the actual quiet traffic leaves, projected from
the existing keypair lifetime frames. No traffic or packet body is repeated. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookTraffic.FrontierFrames
open Leanux Leanux.WG HandshakeJournal

theorem receive_counter (msg : List UInt8) (src : SkbSource) :
    ProductCounterMono (liftWG (wgReceive msg src)) :=
  counter_product (ordinary_counter (Keypairs.WGMore.wgReceive_ordinary msg src))

theorem transmit_counter (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ProductCounterMono (liftWG (wgXmit family addr packets mtu)) :=
  counter_product (ordinary_counter (Keypairs.WGDevice.wgXmit_ordinary family addr packets mtu))

theorem multicast_counter (family addr : Nat) :
    ProductCounterMono (Env.xmitMulticastLoop family addr) :=
  product_snapshot_counter (Keypairs.EnvFrames.xmitMulticastLoop_sameSnapshot family addr)

theorem drained_counter (what : String) (queues : List Bool) :
    ProductCounterMono (Env.requireDrained what queues) :=
  product_snapshot_counter (Keypairs.EnvFrames.requireDrained_sameSnapshot what queues)

end Leanux.Proofs.WG.TimerDiscipline.HookTraffic.FrontierFrames
