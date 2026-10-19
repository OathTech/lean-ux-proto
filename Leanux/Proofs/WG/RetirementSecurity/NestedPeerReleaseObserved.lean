import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseNeutral
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseProjection
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalDecorations
import Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumptionSource

/-! Nested native repayments observe the actual final-reference disposal cut.
The old pre-write acceptance and completed-cookie receipts remain at their
original points, and erasure retains both native Stop results and old history. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
open HandshakeSecurity
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def observedOps (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) : Ops (WGPrefix E) where
  step := liftWGPrefix
  release := StagedDisposal.Decoration.release record decode

theorem observedOps_erases (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) : Ops.Erases (observedOps record decode) where
  step := erasesStatePrefix_lift
  release := fun peer => focusStatePrefix_erases _ _ (StagedDisposal.release_erases peer)

theorem observedOps_projects (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (record e) = none) : Ops.Projects ρ (observedOps record decode) lifted where
  step := by intro α action; change StateProjectsPrefix ρ id (liftWGPrefix action) (liftWGPrefix action); handshake_worker_project_step ρ
  release := StagedDisposal.Decoration.release_projects record decode ρ quiet

/-- Capturing an enriched action retains the same native endpoints and value;
the incoming history and any disposal preceding Stop are kept. -/
theorem capture_projects (ρ : E → Option F) {g : WGPrefix E α} {t : WGPrefix F α}
    (same : StateProjectsPrefix ρ id g t) :
    StateProjectsPrefix ρ id (captureWGObserved g) (captureWGObserved t) := by
  intro w a h
  have projected := same w a h
  change runWGPrefix t w a (h.filterMap ρ) =
    ((runWGPrefix g w a h).1.map (fun ((x,v),b) => ((x,v),b)),
      (runWGPrefix g w a h).2.filterMap ρ) at projected
  change runWGPrefix (captureWGObserved t) w a (h.filterMap ρ) =
    ((runWGPrefix (captureWGObserved g) w a h).1.map (fun ((x,v),b) => ((x,v),b)),
      (runWGPrefix (captureWGObserved g) w a h).2.filterMap ρ)
  rw [runWGPrefix_captureWGObserved, runWGPrefix_captureWGObserved, projected]
  cases hr : runWGPrefix g w a h with
  | mk result hist =>
    cases result with
    | error err => rfl
    | ok out => rcases out with ⟨⟨x,v⟩,b⟩; rfl

def admitInitiationWith (o : Ops (WGPrefix E)) (record : HandshakeAdmission → E)
    (mac : HandshakeMac) : WGPrefix E (Option PeerId) := do
  let checked ← captureWGObserved (initiationCheckWith o mac.input)
  if checked.value.isSome then emitStatePrefix (record (.initiation mac checked))
  liftWGPrefix (initiationAcceptedContinue mac.input checked.value)

def admitResponseWith (o : Ops (WGPrefix E)) (record : HandshakeAdmission → E)
    (mac : HandshakeMac) : WGPrefix E (Option PeerId) := do
  let checked ← captureWGObserved (responseCheckWith o mac.input)
  if checked.value.isSome then emitStatePrefix (record (.response mac checked))
  liftWGPrefix (responseAcceptedContinue mac.input checked.value)

def cookieObserved (o : Ops (WGPrefix E)) (record : CookieConsumption.Receipt → E)
    (msg : Key) : WGPrefix E Unit :=
  receiptWGObserved (cookieWith o msg) (fun run => record ⟨msg,run⟩)

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
