import Leanux.Proofs.WG.Queues.BaseCoherenceStack
import Leanux.Proofs.WG.Queues.BaseCoherenceHandshake
import Leanux.Proofs.WG.Queues.CurrentSlotHistory

/-! Native worker boundaries retain the structural list/table view. Callback
contracts keep the actual product domain; reference deletion and all recorded
Stops remain possible. No account or initialized-input premise is used. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem prepareSource_view : SameView view RxWorkers.prepareSource := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold RxWorkers.prepareSource RxWorkers.publishSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head decryptPacket; exact (decryptPacket_view _).wp (fun s => s=initial))
    | base_rx_step initial

theorem encryptPacket_view (checksum : WG.Packet → Leanux.M WG.Packet)
    (hc : ∀ p, SameView (fun w : World => view w.wg) (checksum p))
    (key : KeypairId) (pkt : DataPacket) :
    SameView (fun w : World => view w.wg) (encryptPacket checksum key pkt) := by
  intro initial
  let P := fun w : World => view w.wg=initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (fun w => view w=initial))
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) := by
    apply PublicationPoll.native_product (fun w => view w=initial)
    simp only [monadLift_self]
    repeat' base_rx_step initial
  have check (p : WG.Packet) : Preserves P (checksum p) := (hc p).wp (fun s => s=initial)
  routing_tx_source [encryptPacket] using [padding,check,keySpec,ambient]

theorem encryptTail_view (item : Option (List SkbId)) :
    SameView (fun w : World => view w.wg) (RxWorkers.encryptTailSource item) := by
  intro initial
  let P := fun w : World => view w.wg=initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) := by
    apply PublicationPoll.native_product (fun w => view w=initial)
    simp only [monadLift_self]
    repeat' base_rx_step initial
  have write (id : SkbId) (f : DataPacket → DataPacket) :
      Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) := by
    apply PublicationPoll.native_product (fun w => view w=initial)
    simp only [monadLift_self]
    repeat' base_rx_step initial
  have publish (xs : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _
      (((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.enqueuePeer_view) xs state).wp (fun s => s=initial))
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) :=
    (encryptPacket_view Env.checksumHelp (fun p => (checksumHelp_sameWorld p).factor (fun w => view w.wg)) key pkt).wp (fun s => s=initial)
  have stepSpec : Preserves P (RxWorkers.encryptStepTailSource item) := by
    routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]
  have needSpec : Preserves P (Env.condResched .encryptWorker) :=
    (product_store_view (condResched_sameKernel _)).wp (fun s => s=initial)
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [stepSpec,needSpec,ambient]

theorem encryptPoll_view : SameView view TxRing.pollSource := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold TxRing.pollSource
  repeat' base_rx_step initial

private theorem sendSkb_structure (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView view (sendSkbToPeer pid bytes ds) := by
  have send4Rule e cache bytes ds exactRx : SameView view (send4 e cache bytes ds exactRx) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.combined_frame)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send4_frame) e cache bytes ds exactRx)
      (ConfiguredHandshake.send4_view e cache bytes ds exactRx)
  have send6Rule e cache bytes ds exactRx : SameView view (send6 e cache bytes ds exactRx) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.combined_frame)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send6_frame) e cache bytes ds exactRx)
      (ConfiguredHandshake.send6_view e cache bytes ds exactRx)
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4; exact (send4Rule _ _ _ _ _).wp (fun s => s=initial))
    | (rx_retention_head send6; exact (send6Rule _ _ _ _ _).wp (fun s => s=initial))
    | base_rx_step initial

private theorem dataSent_structure (pid : PeerId) : SameView view (timersDataSent pid) := by
  have arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64) : SameView view (armTimer pid timer delay jc) := by
    have passive : SameView DurableHolders.passiveView (armTimer pid timer delay jc) :=
      (pinned_const _private.Leanux.Proofs.WG.Queues.PassiveHolders.«0».Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders.arm_preserves) pid timer delay jc
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.list_configured)
      (passive.of_factor Prod.fst slots (fun _ => rfl)) (ConfiguredIdentity.armTimer_view pid timer delay jc)
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold timersDataSent modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w => view w=initial))
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => view w=initial))
    | (rx_retention_head armTimer; exact (arm _ _ _ _).wp (fun s => s=initial))
    | base_rx_step initial

private theorem fresh_structure (pid : PeerId) : SameView view (keepKeyFresh pid) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (sendQueued_view _ _).wp (fun s => s=initial))
    | base_rx_step initial

theorem createDataDone_view (pid : PeerId) (item : List SkbId) : SameView view (createDataDone pid item) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold createDataDone timersAnyAuthenticatedPacketSent WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head timersTraversal; exact (traversal_view _).wp (fun s => s=initial))
    | (rx_retention_head delTimer; exact (delTimer_view _ _).wp (fun s => s=initial))
    | (rx_retention_head sendSkbToPeer; exact (sendSkb_structure _ _ _).wp (fun s => s=initial))
    | (rx_retention_head timersDataSent; exact (dataSent_structure _).wp (fun s => s=initial))
    | (rx_retention_head keepKeyFresh; exact (fresh_structure _).wp (fun s => s=initial))
    | base_rx_step initial

theorem txStep_view (pid : PeerId) : SameView view (txStep pid) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold txStep WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head PrevQueue.peek; exact (store_view (prevQueuePeek_sameWGStore _)).wp (fun s => s=initial))
    | (rx_retention_head createDataDone; exact (createDataDone_view _ _).wp (fun s => s=initial))
    | base_rx_step initial

theorem txIter_view (pid : PeerId) (need : Leanux.M Bool)
    (hn : SameView (fun w : World => view w.wg) need) :
    SameView (fun w : World => view w.wg) (txIter pid need) := by
  intro initial
  let P := fun w : World => view w.wg=initial
  change Preserves P _
  have step : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product _ _ ((txStep_view pid).wp (fun s => s=initial))
  have needSpec : Preserves P need := hn.wp (fun s => s=initial)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  routing_tx_source [txIter,workerIter] using [step,needSpec,ambient]

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
