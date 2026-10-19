import Leanux.Proofs.WG.TransmitSecurity.StagedSourceOrigins
import Leanux.Proofs.WG.TransmitSecurity.StagedHandshakeFrames
import Leanux.Proofs.WG.Queues.RxRingHandshake

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal

theorem epoch_rx_ring {action : WG.M α} (same : SameView RxRing.nativeCell action) :
    SameView Packets.epoch action :=
  same.of_factor (fun cell => cell.map Prod.fst) Packets.epoch
    (fun _ => by simp only [RxRing.nativeCell,Packets.epoch,Option.map_map,Function.comp_def])

theorem Native.initiation (msg : List UInt8) : Preserves (Inv h) (consumeInitiation msg) :=
  frame (epoch_rx_ring (RxRing.consumeInitiation_cell msg)) (Staged.initiation msg)

theorem Native.response (msg : List UInt8) : Preserves (Inv h) (consumeResponse msg) :=
  frame (epoch_rx_ring (RxRing.consumeResponse_cell msg)) (Staged.response msg)

theorem Native.session (pid : PeerId) : Preserves (Inv h) (beginSession pid) :=
  frame (epoch_rx_ring (RxRing.beginSession_cell pid)) (Staged.session pid)

theorem Native.confirm (pid : PeerId) (kid : KeypairId) : Preserves (Inv h) (receivedWithKeypair pid kid) :=
  frame (epoch_rx_ring (RxRing.receivedWithKeypair_cell pid kid)) (Staged.confirm pid kid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
