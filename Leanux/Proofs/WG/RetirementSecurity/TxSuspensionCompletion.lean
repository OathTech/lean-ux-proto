import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionSocket

/-! A successful native TX completion/disposal never removes a suspended
actor. The real scheduler alone moves that actor between active and suspended
states; the WG worker's packet and reference disposal is retained in full. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem queue_peek (queue : PrevQueue α) : Keeps queue.peek := by
  suspension_source [PrevQueue.peek,PrevQueue.dequeue] using [branch,invariant,unsupported]

theorem complete (pid : PeerId) (items : List SkbId) : Keeps (createDataDone pid items) := by
  suspension_source [createDataDone,timersAnyAuthenticatedPacketSent,WG.andM] using [traversal,delete,packet,branch,send_packet,data_sent,fresh]

theorem tx_step (pid : PeerId) : Keeps (txStep pid) := by
  suspension_source [txStep,WG.andM] using [queue_peek,peer,set_peer,packet,branch,invariant,complete,free_packet,key_put,peer_put]

theorem tx_iteration (pid : PeerId) {need : WG.M Bool} (frame : Keeps need) : Keeps (txIter pid need) := by
  unfold txIter workerIter
  repeat' first
    | exact frame
    | exact tx_step pid
    | env_operation_fact branch
    | suspension_step

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
