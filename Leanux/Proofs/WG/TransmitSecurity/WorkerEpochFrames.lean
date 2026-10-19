import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrames

/-! Native packet reads preserve the device epoch used by encryption identities. -/
namespace Leanux.Proofs.WG.TransmitSecurity.WorkerEpochs
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem read_epoch (id : SkbId) :
    SameView (fun w : World => PacketOrigins.epoch w.wg) (liftWG (getTxSkb id)) := by
  apply sameView_liftWG _ PacketOrigins.epoch
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a packet v b run
    exact congrArg PacketOrigins.epoch (Packets.getTxSkb_current id w v packet a b run).1
  · intro _ _ _ same; exact same

end Leanux.Proofs.WG.TransmitSecurity.WorkerEpochs
