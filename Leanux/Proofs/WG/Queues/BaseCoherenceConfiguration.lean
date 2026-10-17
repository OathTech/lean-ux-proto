import Leanux.Proofs.WG.Queues.BaseCoherenceRemoval
import Leanux.Proofs.WG.Queues.PassiveHolders
import Leanux.Proofs.WG.Origins.CurrentConfiguration

/-! Structural coherence through the original acquired-peer configuration
tail and update. Staged sends may acquire, queue or release references; none
of those changes the live-base list or public-key table. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Configuration

private theorem list_configured {α : Type} {action : WG.M α}
    (list : SameView slots action) (configured : SameView ConfiguredIdentity.view action) :
    SameView view action :=
  list.product (configured.of_factor
    (fun s : Option ConfiguredIdentity.State => (s.map ConfiguredIdentity.State.rows).getD [])
    rows (fun _ => by simp only [rows,ConfiguredIdentity.view,ConfiguredIdentity.state,
      Option.map_map,Function.comp_def]))

private theorem key_read (kid : KeypairId) : SameView view (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a key v b run
  exact congrArg view (KeyTimes.getKeypair_return kid w v key a b run).1

private theorem key_write (kid : KeypairId) (key : Keypair) : SameView view (setKeypair kid key) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_update)
    _ (fun _ => rfl) (fun _ => rfl)

private theorem skb_frame (action : SkbM α) : SameView view (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d store hi hd
  simpa only [view,slots,rows,hd,Option.map_some,Option.getD_some] using hi

macro "base_config_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getKeypair; exact (key_read _).wp (fun s => s = $initial))
  | (rx_retention_head setKeypair; exact (key_write _ _).wp (fun s => s = $initial))
  | (rx_retention_head getTxSkb; unfold getTxSkb)
  | (rx_retention_head setTxSkb; unfold setTxSkb)
  | (rx_retention_head newTxSkb; unfold newTxSkb)
  | (rx_retention_head freeTxSkb; unfold freeTxSkb)
  | (rx_retention_head liftSkb; exact (skb_frame _).wp (fun s => s = $initial))
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => view w = $initial))
  | (rx_retention_head peerPut; exact (peerPut_view _).wp (fun s => s = $initial))
  | base_structure_step $initial)

theorem peerGet_view (pid : PeerId) : SameView view (peerGet pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,unsupported]
  repeat' base_config_step initial

private theorem keyGet_view (kid : Option KeypairId) : SameView view (keypairGet kid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' base_config_step initial

private theorem keyPut_view (kid : Option KeypairId) (now : Bool) : SameView view (keypairPut kid now) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' base_config_step initial

macro "base_traffic_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head peerGet; exact (peerGet_view _).wp (fun s => s = $initial))
  | (rx_retention_head keypairGet; exact (keyGet_view _).wp (fun s => s = $initial))
  | (rx_retention_head keypairPut; exact (keyPut_view _ _).wp (fun s => s = $initial))
  | base_config_step $initial)

theorem sendQueued_view (pid : PeerId) (retry : Bool) :
    SameView view (sendQueuedHandshakeInitiation pid retry) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' base_traffic_step initial

private theorem choose_view (pid : PeerId) : SameView view (cpumaskChooseOnline pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold cpumaskChooseOnline
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' base_traffic_step initial

private theorem enqueueDevice_view (pid : PeerId) (item : List SkbId) :
    SameView view (enqueuePerDeviceAndPeer pid item) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold enqueuePerDeviceAndPeer
  simp (config := {zeta := false}) only [branch,queueDeviceWork,invariant]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom
       exact ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_store)
         (cpumaskNextOnlineFrom_sameStore _)).wp (fun s => s = initial))
    | base_traffic_step initial

private theorem enqueuePeer_view (item : List SkbId) (state : PacketState) :
    SameView view (enqueuePerPeerTx item state) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline; exact (choose_view _).wp (fun s => s = initial))
    | base_traffic_step initial

private theorem createData_view (pid : PeerId) (item : List SkbId) : SameView view (createData pid item) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact (enqueueDevice_view _ _).wp (fun s => s = initial))
    | (rx_retention_head enqueuePerPeerTx; exact (enqueuePeer_view _ _).wp (fun s => s = initial))
    | base_traffic_step initial

private theorem noKey_view (pid : PeerId) (packets : List WG.Packet)
    (keypair : Option KeypairId) (invalid : Bool) : SameView view (stagedOutNokey pid packets keypair invalid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (sendQueued_view _ _).wp (fun s => s = initial))
    | base_traffic_step initial

private theorem submit_view (pid kid : Nat) (packets : List DataPacket) :
    SameView view (stagedSubmit pid kid packets) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold stagedSubmit Affiliation.sendAcquire
  repeat' first
    | (rx_retention_head createData; exact (createData_view _ _).wp (fun s => s = initial))
    | (rx_retention_head List.mapM
       apply mapM_view_spec view (fun s => s = initial)
       intro packet
       change Preserves (fun w => view w = initial) _)
    | base_traffic_step initial

private theorem stagedKey_view (pid kid : Nat) (packets : List WG.Packet) :
    SameView view (stagedKeySource pid kid packets) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold stagedKeySource
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact (noKey_view _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head stagedSubmit; exact (submit_view _ _ _).wp (fun s => s = initial))
    | (rx_retention_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).wp (fun w => view w = initial))
    | base_traffic_step initial

/-- Every normal staged-send return retains the structural fields, including
key/refcount guards, queue refusals, restored packets and nullable releases. -/
theorem staged_view (pid : PeerId) : SameView view (sendStagedPackets pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  rw [← stagedFullSource_eq]
  unfold stagedFullSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact (noKey_view _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head stagedKeySource; exact (stagedKey_view _ _ _).wp (fun s => s = initial))
    | base_traffic_step initial

theorem keepalive_view (pid : PeerId) : SameView view (sendKeepalive pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold sendKeepalive
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head sendStagedPackets; exact (staged_view _).wp (fun s => s = initial))
    | base_traffic_step initial

theorem endpoint_view (pid : PeerId) (e : Endpoint) : SameView view (setPeerEndpoint pid e) := by
  have passive : SameView DurableHolders.passiveView (setPeerEndpoint pid e) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.PassiveHolders.«0».Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders.endpoint_preserves) pid e
  exact list_configured (passive.of_factor Prod.fst slots (fun _ => rfl))
    (ConfiguredReceiveLeaves.setPeerEndpoint_view pid e)

theorem listDel_view (id : NodeId) : SameView view (listDel id) :=
  list_configured ((BaseRemoval.listDel_view id).of_factor
    (fun s => s.2.getD []) slots (fun _ => rfl)) (ConfiguredIdentity.listDel_view id)

theorem removeByPeer_view (pid : PeerId) : SameView view (removeByPeer pid) :=
  list_configured ((BaseRemoval.removeByPeer_view pid).of_factor
    (fun s => s.2.getD []) slots (fun _ => rfl)) (ConfiguredIdentity.removeByPeer_view pid)

private theorem aip_frame (action : AipM α) : SameView view (liftAip action) := by
  intro initial
  apply hoare_liftAip
  intro w d store hi hd
  simpa only [view,slots,rows,hd,Option.map_some,Option.getD_some] using hi

private theorem listAdd_view (pid : PeerId) (id : NodeId) : SameView view (listAddTail pid id) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold listAddTail
  repeat' base_config_step initial

macro "base_allowedip_step " initial:term : tactic => `(tactic| first
  | (allocation_release_lift_from AipM; exact (aip_frame _).wp (fun s => s = $initial))
  | (rx_retention_head liftAip; exact (aip_frame _).wp (fun s => s = $initial))
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; unfold invariant)
  | base_config_step $initial)

private theorem add_view (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView view (add root bits key cidr peer) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact (listAdd_view _ _).wp (fun s => s = initial))
    | (rx_retention_head listDel; exact (listDel_view _).wp (fun s => s = initial))
    | base_allowedip_step initial

private theorem insert_view (family addr cidr : Nat) (pid : PeerId) :
    SameView view (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact (add_view _ _ _ _ _).wp (fun s => s = initial))
    | base_allowedip_step initial

theorem setAllowedip_view (pid : PeerId) (ip : AllowedIpAttrs) : SameView view (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact (insert_view _ _ _ _).wp (fun s => s = initial))
    | base_allowedip_step initial

/-- The full tail is an exact structural frame even for a nullable peer
unrelated to pid; its final release is the actual source call. -/
theorem tailFinish_view (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    SameView view (peerTailFinishSource a peer pid ret) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold peerTailFinishSource WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head sendKeepalive; exact (keepalive_view _).wp (fun s => s = initial))
    | (rx_retention_head sendStagedPackets; exact (staged_view _).wp (fun s => s = initial))
    | base_config_step initial

theorem tail_view (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    SameView view (peerConfigTailSource a peer pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self,branch]
  repeat' first
    | (rx_retention_head setAllowedip; exact (setAllowedip_view _ _).wp (fun s => s = initial))
    | (rx_retention_head peerTailFinishSource; exact (tailFinish_view _ _ _ _).wp (fun s => s = initial))
    | base_config_step initial

/-- Update preserves coherence without requiring acquired-peer equality,
funding, residency or configured identity. Removal changes both fields together. -/
theorem update_preserves (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    Preserves Inv (peerConfigUpdateSource a peer flags psk pid) := by
  have framed {α : Type} {action : WG.M α} (same : SameView view action) : Preserves Inv action :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.preserves_of_view) same
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerRemove; exact peerRemove_preserves _)
    | (rx_retention_head setPeerEndpoint; exact framed (endpoint_view _ _))
    | (rx_retention_head removeByPeer; exact framed (removeByPeer_view _))
    | (rx_retention_head peerConfigTailSource; exact framed (tail_view _ _ _))
    | (rx_retention_head peerPut; exact framed (peerPut_view _))
    | (rx_retention_head getPeer
       exact framed ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_read) _))
    | (rx_retention_head setPeer
       exact framed ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_write) _ _))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
