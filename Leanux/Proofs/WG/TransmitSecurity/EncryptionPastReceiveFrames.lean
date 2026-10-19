import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastTimers
import Leanux.Proofs.WG.Queues.TxLiveRxCompletion

/-! Receive-side leaf contracts retain historical encryption exclusion. The
allowed-IP lookup pays attention to the actual nullable borrow; confirmation
may release old keys but cannot republish an old packet into encryption work. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition RetirementSecurity
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem ready_store {action : WG.M α} (same : SameWGStore action) :
    Preserves (Ready past active) action :=
  ready_frame (LiveFrontier.store_ready _ same) (store same)

theorem ready_modify (f : Device → Device)
    (metadata : ∀ d, deviceAllocationMetadata (f d) = deviceAllocationMetadata d)
    (ring : ∀ d, (f d).encryptQueue = d.encryptQueue) :
    Preserves (Ready past active) (modifyDev f) :=
  ready_frame (LiveFrontier.ready_frame (metadata_modifyDev f metadata)
    (TxRing.modify f (fun d => congrArg DeviceAllocationMetadata.epoch (metadata d)) ring))
    (modify f metadata ring)

theorem ready_index (action : IndexM α) : Preserves (Ready past active) (liftIndex action) := by
  apply ready_frame ?_ (index action)
  apply hoare_liftIndex
  intro w d table before device
  simpa only [LiveFrontier.Ready,LiveFrontier.Inv,LiveFrontier.Physical,device,Option.some.injEq,forall_eq'] using before

macro "encryption_past_receive_step" : tactic => `(tactic| first
  | (rx_retention_head requireNotPending; unfold requireNotPending)
  | (rx_retention_head getKeypair; exact ready_read_key _)
  | (rx_retention_head setKeypair; exact ready_set_key _ _)
  | (rx_retention_head peerGet; exact ready_frame (LiveFrontier.peer_get _) (peer_get _))
  | (rx_retention_head peerPut; exact ready_frame (LiveFrontier.peer_put _) (peer_put _))
  | (rx_retention_head keypairPut; exact ready_frame (LiveFrontier.key_put _ _) (key_put _ _))
  | (rx_retention_head modifyDev; apply ready_modify; all_goals intro d; rfl)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Ready _ _))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from IndexM; exact ready_index _)
  | (allocation_release_lift_from Net.M; exact ready_store (liftRouting_sameWGStore _))
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head MonadStateOf.get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
  | (rx_retention_head ForIn.forIn; apply list_view_spec id (Ready _ _); intro x b; change Preserves (Ready _ _) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | encryption_past_ready_step)

theorem ready_cache (pid : PeerId) : Preserves (Ready past active) (dstCacheReset pid) := by
  unfold dstCacheReset
  material_lower
  repeat' encryption_past_receive_step

theorem ready_endpoint (pid : PeerId) (endpoint : Endpoint) :
    Preserves (Ready past active) (setPeerEndpoint pid endpoint) := by
  unfold setPeerEndpoint
  material_lower
  repeat' first
    | (rx_retention_head endpointEq; exact ready_store (endpointEq_sameStore _ _))
    | (rx_retention_head dstCacheReset; exact ready_cache _)
    | encryption_past_receive_step

theorem ready_lookup (family : Nat) (bytes : List UInt8) :
    Preserves (Ready past active) (lookupSrc family bytes) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec family bytes (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at borrowed
    have device := congrArg WGStoreView.dev borrowed
    have epochs := congrArg WGStoreView.netIfindexNext borrowed
    change v.dev = w.dev at device
    change v.netIfindexNext = w.netIfindexNext at epochs
    simpa only [Ready,LiveFrontier.Ready,LiveFrontier.Inv,LiveFrontier.Physical,view,device,epochs] using before
  | some pid =>
    obtain ⟨d,p,device,_,_,same⟩ := borrowed
    change w.dev = some d at device
    have endpoint := congrArg WGStoreView.dev same
    have epochs := congrArg WGStoreView.netIfindexNext same
    change v.netIfindexNext = w.netIfindexNext at epochs
    change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} at endpoint
    simpa only [Ready,LiveFrontier.Ready,LiveFrontier.Inv,LiveFrontier.Physical,view,
      device,endpoint,epochs,Option.map_some,Option.some.injEq,forall_eq'] using before

theorem ready_stats (pid : PeerId) (len : Nat) : Preserves (Ready past active) (updateRxStats pid len) := by
  unfold updateRxStats
  repeat' encryption_past_receive_step

theorem ready_dishonest (why : Dishonest) : Preserves (Ready past active) (dishonest why) := by
  cases why <;> unfold dishonest <;> repeat' encryption_past_receive_step

theorem ready_received (pid kid : Nat) : Preserves (Ready past active) (receivedWithKeypair pid kid) := by
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' encryption_past_receive_step

theorem ready_fresh (pid : PeerId) : Preserves (Ready past active) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact ready_frame (LiveFrontier.queued _ _) (queued _ _))
    | encryption_past_receive_step

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
