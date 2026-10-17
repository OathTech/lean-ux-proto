import Leanux.Proofs.WG.Queues.TxLiveStaging

/-! The full native staged-send source retains numeric bounds on logical live
TX ring items and the existing physical ring witness. No packet residency,
key-owner validity or reference-count premise is added. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do RxCredits

private theorem empty_safe {action : WG.M α} (h : Preserves (Safe []) action) : Preserves Ready action :=
  hoare_consequence h (fun _ hi=>⟨hi,fun _ _ _ member=>by contradiction⟩) (fun _ _ hi=>hi.1)

theorem ready_frame {action : WG.M α} (metadata : SameView allocationMetadata action)
    (ring : SameView TxRing.nativeCell action) : Preserves Ready action :=
  empty_safe (frame [] metadata ring)

private theorem read_peer (pid : PeerId) : Preserves Ready (getPeer pid) :=
  empty_safe ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStaging.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.read_peer) [] pid)

private theorem read_key (kid : KeypairId) : Preserves Ready (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b hi run
  simpa only [(KeyTimes.getKeypair_return kid w v k a b run).1] using hi

private theorem modify_ready (f : Device→Device)
    (metadata : ∀d,deviceAllocationMetadata (f d)=deviceAllocationMetadata d)
    (epoch : ∀d,(f d).ifindex=d.ifindex) (ring : ∀d,(f d).encryptQueue=d.encryptQueue) :
    Preserves Ready (modifyDev f) :=
  ready_frame (metadata_modifyDev f metadata) (TxRing.modify f epoch ring)

private theorem index_ready (action : IndexM α) : Preserves Ready (liftIndex action) := by
  apply hoare_liftIndex
  intro w d table hi hd
  simpa only [Ready,Inv,Physical,hd,Option.some.injEq,forall_eq'] using hi

macro "live_send_step" : tactic => `(tactic| first
  | rxstack_preserves_join
  | (allocation_release_head getPeer; exact read_peer _)
  | (allocation_release_head getKeypair; exact read_key _)
  | (allocation_release_head getDev; unfold getDev)
  | (allocation_release_head setPeer; exact ready_frame (setPeer_metadata _ _) (TxRing.setPeer_frame _ _))
  | (allocation_release_head setKeypair; unfold setKeypair)
  | (allocation_release_head modifyDev; apply modify_ready; all_goals intro d; rfl)
  | (allocation_release_head get; exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
  | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) Ready)
  | (allocation_release_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp Ready)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact index_ready _)
  | (allocation_release_head ForIn.forIn; apply list_view_spec id Ready; intro x b; change Preserves Ready _)
  | (allocation_release_head modify; apply hoare_modify; intro w hi; exact hi)
  | allocation_release_step)

theorem peer_get (pid : PeerId) : Preserves Ready (peerGet pid) :=
  ready_frame (peerGet_metadata pid) (TxRing.peerGet_frame pid)

theorem peer_put (pid : Option PeerId) : Preserves Ready (peerPut pid) :=
  ready_frame (peerPut_metadata pid) (TxRing.peerPut_frame pid)

theorem key_put (kid : Option KeypairId) (now : Bool) : Preserves Ready (keypairPut kid now) :=
  ready_frame ((keypairPut_rest kid now).factor (fun rest=>rest.2.2)) (TxRing.keypairPut_frame kid now)

theorem key_get (kid : Option KeypairId) : Preserves Ready (keypairGet kid) := by
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' live_send_step

theorem queued (pid : PeerId) (retry : Bool) : Preserves Ready (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (allocation_release_head peerGet; exact peer_get _)
    | (allocation_release_head peerPut; exact peer_put _)
    | live_send_step

/-- The original rejection tail retains the bound while invalidating/repaying
its optional key, visiting orphan choices, restoring staged packets and queueing. -/
theorem no_key (pid : PeerId) (packets : List WG.Packet) (key : Option KeypairId) (invalid : Bool) :
    Preserves Ready (stagedOutNokey pid packets key invalid) := by
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head keypairPut; exact key_put _ _)
    | (allocation_release_head sendQueuedHandshakeInitiation; exact queued _ _)
    | live_send_step

/-- The actual key-selected continuation keeps all key checks and the recorded
nonce loop before the fresh-allocation submission. -/
theorem key_source (pid kid : Nat) (packets : List WG.Packet) :
    Preserves Ready (stagedKeySource pid kid packets) := by
  have getter := read_key kid
  have setter (id : KeypairId) (key : Keypair) : Preserves Ready (setKeypair id key) := by
    apply modify_ready <;> intro d <;> rfl
  have expired (date : Int64) : Preserves Ready (branchExpired .stagedBirthdateExpired date REJECT_AFTER_TIME) :=
    (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp Ready
  have ecn (pkt : WG.Packet) : Preserves Ready (ipTunnelEcnEncap pkt) :=
    (ipTunnelEcnEncap_sameWGWorld pkt).wp Ready
  have out := no_key pid packets (some kid)
  have submit := staged_submit pid kid
  have loop {α β : Type} (xs : List α) (init : β) (f : α→β→WG.M (ForInStep β))
      (hf : ∀x b,Preserves Ready (f x b)) : Preserves Ready (forIn xs init f) :=
    list_view_spec id Ready xs init f hf
  have ambient {α : Type} (a : AmbientM α) : Preserves Ready (monadLift a : WG.M α) := hoare_liftAmbient a Ready
  rxstack_preserves_source [stagedKeySource,branch,branchCmp]
    using [getter,setter,expired,ecn,out,submit,loop,ambient]

/-- Full native staged send preserves the live ring frontier on normal return,
including empty/no-key/refusal arms. Original guards retain their Stop behavior. -/
theorem send (pid : PeerId) : Preserves Ready (sendStagedPackets pid) := by
  have read := read_peer
  have write (id : PeerId) (peer : Peer) : Preserves Ready (setPeer id peer) :=
    ready_frame (setPeer_metadata id peer) (TxRing.setPeer_frame id peer)
  have key := key_get
  have out := no_key
  have source := key_source
  have ambient {α : Type} (a : AmbientM α) : Preserves Ready (monadLift a : WG.M α) := hoare_liftAmbient a Ready
  rw [← stagedFullSource_eq]
  rxstack_preserves_source [stagedFullSource,branch,invariant] using [read,write,key,out,source,ambient]

theorem keepalive (pid : PeerId) : Preserves Ready (sendKeepalive pid) := by
  unfold sendKeepalive
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (allocation_release_head sendStagedPackets; exact send _)
    | live_send_step

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
