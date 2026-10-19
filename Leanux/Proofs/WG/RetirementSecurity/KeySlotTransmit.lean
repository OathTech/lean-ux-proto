import Leanux.Proofs.WG.RetirementSecurity.KeySlotWorkers

/-! Native TX staging and admission change queues and packet cells while
retaining the published-slot/liveness relation. DEAD and ring-refusal arms
remain actual disposal paths; this projection alone makes no progress claim. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem skb (action : SkbM α) : Preserves (InvExcept pending) (liftSkb action) := by
  apply hoare_liftSkb
  intro w d packets before device
  apply peers before
  simp only [peersAt,device,Option.map_some]

macro "key_slot_tx_step" : tactic => `(tactic| first
  | (rx_retention_head getTxSkb; unfold getTxSkb)
  | (rx_retention_head setTxSkb; unfold setTxSkb)
  | (rx_retention_head newTxSkb; unfold newTxSkb)
  | (rx_retention_head freeTxSkb; unfold freeTxSkb)
  | (rx_retention_head liftSkb; exact skb _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (InvExcept _)
     intro x b
     change Preserves (InvExcept _) _)
  | (rx_retention_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (InvExcept _))
  | key_slot_work_step)

theorem key_get (word : Option KeypairId) : Preserves (InvExcept pending) (keypairGet word) := by
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta:=false}) only [branch,branchCmp,invariant,unsupported]
  repeat' key_slot_tx_step

theorem send_queued (pid : PeerId) (retry : Bool) :
    Preserves (InvExcept pending) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta:=false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' key_slot_tx_step

theorem choose_cpu (pid : PeerId) : Preserves (InvExcept pending) (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp (config := {zeta:=false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' key_slot_tx_step

theorem enqueue (pid : PeerId) (item : List SkbId) :
    Preserves (InvExcept pending) (enqueuePerDeviceAndPeer pid item) := by
  unfold enqueuePerDeviceAndPeer
  simp (config := {zeta:=false}) only [branch,queueDeviceWork,invariant]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom; exact store (cpumaskNextOnlineFrom_sameStore _))
    | key_slot_tx_step

theorem publish_tx (item : List SkbId) (state : PacketState) :
    Preserves (InvExcept pending) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp (config := {zeta:=false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline; exact choose_cpu _)
    | key_slot_tx_step

theorem create_data (pid : PeerId) (item : List SkbId) :
    Preserves (InvExcept pending) (createData pid item) := by
  unfold createData
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueue _ _)
    | (rx_retention_head enqueuePerPeerTx; exact publish_tx _ _)
    | key_slot_tx_step

theorem no_key (pid : PeerId) (packets : List WG.Packet) (key : Option KeypairId) (invalid : Bool) :
    Preserves (InvExcept pending) (stagedOutNokey pid packets key invalid) := by
  unfold stagedOutNokey
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact send_queued _ _)
    | key_slot_tx_step

theorem submit (pid kid : Nat) (packets : List DataPacket) :
    Preserves (InvExcept pending) (stagedSubmit pid kid packets) := by
  unfold stagedSubmit Affiliation.sendAcquire
  repeat' first
    | (rx_retention_head createData; exact create_data _ _)
    | (rx_retention_head List.mapM
       apply mapM_view_spec id (InvExcept pending)
       intro packet
       change Preserves (InvExcept pending) _)
    | key_slot_tx_step

theorem staged_key (pid kid : Nat) (packets : List WG.Packet) :
    Preserves (InvExcept pending) (stagedKeySource pid kid packets) := by
  unfold stagedKeySource
  simp (config := {zeta:=false}) only [branch,branchCmp]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact no_key _ _ _ _)
    | (rx_retention_head stagedSubmit; exact submit _ _ _)
    | (rx_retention_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).wp (InvExcept pending))
    | key_slot_tx_step

theorem staged (pid : PeerId) : Preserves (InvExcept pending) (sendStagedPackets pid) := by
  rw [←stagedFullSource_eq]
  unfold stagedFullSource
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact no_key _ _ _ _)
    | (rx_retention_head stagedKeySource; exact staged_key _ _ _)
    | (rx_retention_head keypairGet; exact key_get _)
    | key_slot_tx_step

theorem keepalive (pid : PeerId) : Preserves (InvExcept pending) (sendKeepalive pid) := by
  apply HolderKeepalive.rule _ pid (staged pid)
  intro mtu
  exact update pid (fun p=>{p with staged:=p.staged++[{mtu:=mtu}]}) (fun _ h=>h) (fun _ h=>h)

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
