import Leanux.Proofs.WG.Keypairs.Evolution.Scheduler
import Leanux.Proofs.WG.TimerDiscipline.HookStateFrames
/-! Physical keypair-snapshot frames for decrypt publication and transmit polling. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookState
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Keypairs Keypairs.WGFrames Keypairs.WGTransitions Keypairs.WGMore Keypairs.EnvFrames
theorem prepare_snapshot : SameSnapshot RxWorkers.prepareSource := by
  have publication (id : SkbId) (state : PacketState) : SameSnapshot (RxWorkers.publishSource id state) := by
    snapshot_source [RxWorkers.publishSource] using
      [ownerPeerDeref_sameSnapshot,peerGet_sameSnapshot,getPeer_sameSnapshot,setPeer_sameSnapshot]
  snapshot_source [RxWorkers.prepareSource] using
    [getDev_sameSnapshot,WGMore.decryptPacket_sameSnapshot]
  all_goals exact publication _ _

theorem poll_snapshot : SameSnapshot TxRing.pollSource := by
  snapshot_source [TxRing.pollSource] using [getDev_sameSnapshot]
end Leanux.Proofs.WG.TimerDiscipline.HookState
