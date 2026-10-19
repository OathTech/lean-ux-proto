import Leanux.Proofs.WG.RetirementSecurity.KeySlotLifecycle
import Leanux.Proofs.WG.Origins.CurrentRx

/-! Native RX completion and TX disposal transport live slot publication.
Routing lookup acquires its actual peer before payment; authenticated promotion
uses the separately proved source guard and cannot resurrect dead slots. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem lookup_source (protocol : Nat) (bytes : List UInt8) :
    Preserves (InvExcept pending) (lookupSrc protocol bytes) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w a result v b rfl run
  cases result with
  | none=>exact device before (congrArg WGStoreView.dev borrowed)
  | some pid=>
    obtain ⟨d,p,hd,hp,_,out⟩ := borrowed
    exact device (replace before hd hp (q:={p with refcount:=p.refcount+1}) (fun h=>h) (fun h=>h))
      (congrArg WGStoreView.dev out)

theorem fresh_rx (pid : PeerId) : Preserves (InvExcept pending) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact send_queued _ _)
    | key_slot_rx_step

theorem stats (pid : PeerId) (len : Nat) : Preserves (InvExcept pending) (updateRxStats pid len) := by
  unfold updateRxStats
  repeat' key_slot_rx_step

theorem reject (why : Dishonest) : Preserves (InvExcept pending) (dishonest why) := by
  cases why <;> exact modify _ (fun _=>rfl)

theorem consume_done (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Preserves (InvExcept pending) (consumeDataDone pid pkt e) := by
  unfold consumeDataDone WG.andM WG.orM
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerEndpoint; exact endpoint _ _)
    | (rx_retention_head receivedWithKeypair; exact confirmation _ _)
    | (rx_retention_head sendStagedPackets; exact staged _)
    | (rx_retention_head keepKeyFreshRx; exact fresh_rx _)
    | (rx_retention_head timersHandshakeComplete; exact complete _ _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact del_timer _ _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head timersDataReceived; exact received_timer _)
    | (rx_retention_head updateRxStats; exact stats _ _)
    | (rx_retention_head dishonest; exact reject _)
    | (rx_retention_head lookupSrc; exact lookup_source _ _)
    | (rx_retention_head inetEcnDecapsulate; exact store (inetEcnDecapsulate_sameWGStore _ _ _))
    | key_slot_rx_step

theorem validate_counter (kid : KeypairId) (nonce : Nat) :
    Preserves (InvExcept pending) (counterValidate kid nonce) := by
  unfold counterValidate WG.orM
  simp (config := {zeta:=false}) only [branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' key_slot_rx_step

theorem decrypt_packet (pkt : RxPacket) : Preserves (InvExcept pending) (decryptPacket pkt) := by
  unfold decryptPacket WG.orM
  simp (config := {zeta:=false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' first
    | receive_crypto (InvExcept pending)
    | key_slot_rx_step

theorem fresh_tx (pid : PeerId) : Preserves (InvExcept pending) (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta:=false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact send_queued _ _)
    | key_slot_rx_step

theorem sent_timer (pid : PeerId) : Preserves (InvExcept pending) (timersDataSent pid) := by
  unfold timersDataSent
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (InvExcept pending))
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (InvExcept pending))
    | (rx_retention_head modPeerTimerGuard
       exact combined_frame (ConfiguredIdentity.modPeerTimerGuard_view _) (modPeerTimerGuard_ownership _))
    | (rx_retention_head armTimer; exact arm _ _ _ _)
    | key_slot_rx_step

theorem send_skb (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Preserves (InvExcept pending) (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeer
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head send4; exact combined_frame (ConfiguredHandshake.send4_view _ _ _ _ _) (HolderHandshake.socket4_points _ _ _ _ _))
    | (rx_retention_head send6; exact combined_frame (ConfiguredHandshake.send6_view _ _ _ _ _) (HolderHandshake.socket6_points _ _ _ _ _))
    | key_slot_rx_step

theorem data_done (pid : PeerId) (item : List SkbId) : Preserves (InvExcept pending) (createDataDone pid item) := by
  unfold createDataDone WG.andM
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact del_timer _ _)
    | (rx_retention_head sendSkbToPeer; exact send_skb _ _ _)
    | (rx_retention_head timersDataSent; exact sent_timer _)
    | (rx_retention_head keepKeyFresh; exact fresh_tx _)
    | key_slot_rx_step

theorem tx_step (pid : PeerId) : Preserves (InvExcept pending) (txStep pid) := by
  unfold txStep WG.andM
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head PrevQueue.peek; exact store (prevQueuePeek_sameWGStore _))
    | (rx_retention_head createDataDone; exact data_done _ _)
    | key_slot_rx_step

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
