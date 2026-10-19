import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseObservedFrames

/-! The actual old consumer journals are preserved after hiding only the new
nested-disposal events. No completed enclosing consumer is assumed. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
open HandshakeSecurity
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Exact old-journal projection transfers native erasure, including Stop. -/
theorem projects_erases (ρ : E → Option F) {g : WGPrefix E α} {t : WGPrefix F α}
    {native : WG.M α} (projected : StateProjectsPrefix ρ id g t)
    (erased : ErasesStatePrefix t native) : ErasesStatePrefix g native := by
  intro w a h
  have hp := congrArg Prod.fst (projected w a h)
  have he := erased w a (h.filterMap ρ)
  change (runStatePrefix g w a h).1 = _
  have ident : (fun x : (α × WGWorld) × Ambient => (Prod.map id id x.1,x.2)) = id := by
    funext x
    rcases x with ⟨⟨v,w⟩,a⟩
    rfl
  simp only [ident,Except.map_id] at hp
  exact hp.symm.trans he

private theorem emit_matching (ρ : E → Option F) (e : E) (f : F)
    (same : ρ e = some f) :
    StateProjectsPrefix ρ id (emitStatePrefix e : WGPrefix E Unit) (emitStatePrefix f) := by
  intro w a h
  change (Except.ok (ε := Stop) (((),w),a),h.filterMap ρ ++ [f]) =
    (Except.ok (ε := Stop) (((),w),a),(h ++ [e]).filterMap ρ)
  simp [List.filterMap_append,same]

theorem initiation_matching (ρ : E → Option F)
    {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)} (h : Ops.Projects ρ g t)
    (record : HandshakeAdmission → E) (target : HandshakeAdmission → F)
    (same : ∀ e, ρ (record e) = some (target e)) (mac : HandshakeMac) :
    StateProjectsPrefix ρ id (admitInitiationWith g record mac) (admitInitiationWith t target mac) := by
  unfold admitInitiationWith
  apply StateProjectsPrefix.bind ρ id id (capture_projects ρ (initiationCheck_projects ρ h mac.input))
  intro checked
  dsimp only [id]
  repeat' first
    | with_reducible exact emit_matching ρ _ _ (same _)
    | handshake_worker_project_step ρ

theorem response_matching (ρ : E → Option F)
    {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)} (h : Ops.Projects ρ g t)
    (record : HandshakeAdmission → E) (target : HandshakeAdmission → F)
    (same : ∀ e, ρ (record e) = some (target e)) (mac : HandshakeMac) :
    StateProjectsPrefix ρ id (admitResponseWith g record mac) (admitResponseWith t target mac) := by
  unfold admitResponseWith
  apply StateProjectsPrefix.bind ρ id id (capture_projects ρ (responseCheck_projects ρ h mac.input))
  intro checked
  dsimp only [id]
  repeat' first
    | with_reducible exact emit_matching ρ _ _ (same _)
    | handshake_worker_project_step ρ

theorem initiation_lifted (mac : HandshakeMac) :
    admitInitiationWith lifted id mac = admitInitiation mac := by
  unfold admitInitiationWith
  rw [initiationCheck_lifted, initiationCheck_native]
  rfl

theorem response_lifted (mac : HandshakeMac) :
    admitResponseWith lifted id mac = admitResponse mac := by
  unfold admitResponseWith
  rw [responseCheck_lifted, responseCheck_native]
  rfl

/-- Hiding disposal keeps the identical native initiation acceptance receipt,
emitted before its first protocol write even when the continuation stops. -/
theorem initiation_old (release : StagedDisposal.Event → E)
    (releaseDecode : E → Option StagedDisposal.Event)
    (record : HandshakeAdmission → E) (ρ : E → Option HandshakeAdmission)
    (quiet : ∀ e, ρ (release e) = none) (same : ∀ e, ρ (record e) = some e)
    (mac : HandshakeMac) :
    StateProjectsPrefix ρ id (admitInitiationWith (observedOps release releaseDecode) record mac)
      (admitInitiation mac) := by
  rw [←initiation_lifted]
  exact initiation_matching ρ (observedOps_projects release releaseDecode ρ quiet) record id same mac

/-- Response refusal observes its actual repayment; successful acceptance keeps
the original pre-write receipt and every subsequent stopped prefix. -/
theorem response_old (release : StagedDisposal.Event → E)
    (releaseDecode : E → Option StagedDisposal.Event)
    (record : HandshakeAdmission → E) (ρ : E → Option HandshakeAdmission)
    (quiet : ∀ e, ρ (release e) = none) (same : ∀ e, ρ (record e) = some e)
    (mac : HandshakeMac) :
    StateProjectsPrefix ρ id (admitResponseWith (observedOps release releaseDecode) record mac)
      (admitResponse mac) := by
  rw [←response_lifted]
  exact response_matching ρ (observedOps_projects release releaseDecode ρ quiet) record id same mac

/-- The cookie completion receipt is unchanged; a nested release cut remains
in the enriched history even if its later release suffix stops. -/
theorem cookie_old (release : StagedDisposal.Event → E)
    (releaseDecode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none)
    (record : CookieConsumption.Receipt → E) (target : CookieConsumption.Receipt → F)
    (same : ∀ r, ρ (record r) = some (target r)) (msg : Key) :
    StateProjectsPrefix ρ id (cookieObserved (observedOps release releaseDecode) record msg)
      (CookieConsumption.observed target msg) := by
  apply Exchange.receipt_projects ρ _ _ _ _ ?_ (fun _ => same _)
  have projected := cookie_projects ρ (observedOps_projects release releaseDecode ρ quiet) msg
  simpa only [cookie_lifted,cookie_native] using projected

/-- Original queued key retirement executes the observed peer release after
handshake and slot clearing. Its Stop result and projected history are exact. -/
theorem clear_old (release : StagedDisposal.Event → E)
    (releaseDecode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (pid : PeerId) :
    StateProjectsPrefix ρ id (clearWith (observedOps release releaseDecode) pid)
      (liftWGPrefix (queuedExpiredZeroKeyMaterial pid)) := by
  simpa only [clear_lifted,clear_native] using
    clear_projects ρ (observedOps_projects release releaseDecode ρ quiet) pid

theorem flushedClear_old (release : StagedDisposal.Event → E)
    (releaseDecode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (pid : PeerId) :
    StateProjectsPrefix ρ id (flushedClearWith (observedOps release releaseDecode) pid)
      (liftWGPrefix (runFlushedClearWork pid)) := by
  simpa only [flushedClear_lifted,flushedClear_native] using
    flushedClear_projects ρ (observedOps_projects release releaseDecode ρ quiet) pid

/-- The actual RX cleanup observes repayment before its free branch and packet
free; neither later operation must complete for the disposal event to remain. -/
theorem cleanup_old (release : StagedDisposal.Event → E)
    (releaseDecode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (skb : SkbId) (pkt : RxPacket) (flag : Bool) :
    StateProjectsPrefix ρ id (cleanupWith (observedOps release releaseDecode) skb pkt flag)
      (liftWGPrefix (Queues.RxCredits.cleanup skb pkt flag)) := by
  simpa only [cleanup_lifted,cleanup_native] using
    cleanup_projects ρ (observedOps_projects release releaseDecode ρ quiet) skb pkt flag

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
