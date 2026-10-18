import Leanux.Proofs.WG.AuthenticatedEffects.SendQueueFrames

/-! Data submission may alter encrypt/TX queues and release references; it
preserves the independent handshake-work queue used by the causal tickets. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

macro "send_work_frame_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getDev; unfold getDev; simp only [invariant])
  | (rx_retention_head setTxSkb; unfold setTxSkb)
  | (rx_retention_head ForIn.forIn
     first
       | (apply list_view_spec Queues.WorkQueueFrames.view (fun s => s = $initial); intro x state
          change Preserves (fun w => Queues.WorkQueueFrames.view w = $initial) _)
       | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
  | (rx_retention_head get
     exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head keypairPut
     exact (Queues.WorkQueueFrames.keypairPut_frame _ _).wp (fun s => s = $initial))
  | (rx_retention_head peerPut
     exact (Queues.WorkQueueFrames.peerPut_frame _).wp (fun s => s = $initial))
  | (rx_retention_head peerGet
     exact (Queues.WorkQueueFrames.peerGet_frame _).wp (fun s => s = $initial))
  | (rx_retention_head liftSkb
     apply hoare_liftSkb
     intro w d store hi hd
     simpa [Queues.WorkQueueFrames.view,hd] using hi)
  | work_queue_step $initial)

private theorem key_get_work_frame (id : Option KeypairId) :
    SameView Queues.WorkQueueFrames.view (keypairGet id) := by
  intro initial
  change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
  unfold keypairGet refcountIncNotZero
  simp only [branch,branchCmp,invariant,unsupported]
  repeat' send_work_frame_step initial

theorem key_get_frame (id : Option KeypairId) : SameView queue (keypairGet id) :=
  of_workQueueFrame (key_get_work_frame id)

private theorem cpu_choose_frame (pid : PeerId) :
    SameView Queues.WorkQueueFrames.view (cpumaskChooseOnline pid) := by
  intro initial
  change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
  unfold cpumaskChooseOnline
  simp only [branch]
  repeat' send_work_frame_step initial

private theorem enqueue_device_frame (pid : PeerId) (items : List SkbId) :
    SameView Queues.WorkQueueFrames.view (enqueuePerDeviceAndPeer pid items) := by
  intro initial
  change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
  unfold enqueuePerDeviceAndPeer
  simp only [branch,queueDeviceWork,invariant,getDev]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom
       exact (Queues.WorkQueueFrames.store (cpumaskNextOnlineFrom_sameStore _)).wp (fun s => s = initial))
    | send_work_frame_step initial

private theorem enqueue_peer_frame (items : List SkbId) (state : PacketState) :
    SameView Queues.WorkQueueFrames.view (enqueuePerPeerTx items state) := by
  intro initial
  change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
  unfold enqueuePerPeerTx
  simp only [peekQueuedUnit,recordQueued,invariant,getTxSkb,setTxSkb]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline; exact (cpu_choose_frame _).wp (fun s => s = initial))
    | send_work_frame_step initial

theorem create_data_frame (pid : PeerId) (items : List SkbId) : SameView queue (createData pid items) := by
  apply of_workQueueFrame
  intro initial
  change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
  unfold createData
  simp only [branch,invariant,getTxSkb,freeTxSkb]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact (enqueue_device_frame _ _).wp (fun s => s = initial))
    | (rx_retention_head enqueuePerPeerTx; exact (enqueue_peer_frame _ _).wp (fun s => s = initial))
    | send_work_frame_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
