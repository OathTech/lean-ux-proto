import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseContracts
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerObserved

/-! Direct enriched acceptance agrees with the original twice-focused observer
when releases are native. The receipt remains before the native continuation,
including when that continuation stops. Incoming histories are unrestricted. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem focus_native_acceptance (record : F → E) (decode : E → Option F)
    (check : WG.M α) (accept : α → Bool) (event : WGRunWitness α → F)
    (finish : α → WG.M β) :
    focusStatePrefix record decode (do
      let checked ← captureWGRun check
      if accept checked.value then emitStatePrefix (event checked)
      liftWGPrefix (finish checked.value)) = (do
      let checked ← captureWGRun check
      if accept checked.value then emitStatePrefix (record (event checked))
      liftWGPrefix (finish checked.value) : WGPrefix E β) := by
  funext w a h
  change ((runWGPrefix (do
      let checked ← captureWGRun check
      if accept checked.value then emitStatePrefix (event checked)
      liftWGPrefix (finish checked.value)) w a (h.filterMap decode)).1,
    h ++ ((runWGPrefix (do
      let checked ← captureWGRun check
      if accept checked.value then emitStatePrefix (event checked)
      liftWGPrefix (finish checked.value)) w a (h.filterMap decode)).2.drop
        (h.filterMap decode).length).map record) =
    runWGPrefix (do
      let checked ← captureWGRun check
      if accept checked.value then emitStatePrefix (record (event checked))
      liftWGPrefix (finish checked.value)) w a h
  simp only [runWGPrefix,runStatePrefix_bind]
  have capture (hist : List F) := runWGPrefix_captureWGRun check w a hist
  have capture' (hist : List E) := runWGPrefix_captureWGRun check w a hist
  simp only [runWGPrefix] at capture capture'
  rw [capture, capture']
  cases hc : (check.run w).run a with
  | error err => simp [Except.map]
  | ok out =>
    rcases out with ⟨⟨x,v⟩,b⟩
    simp only [Except.map]
    split <;> simp [runStatePrefix_bind,runStatePrefix_emit,liftWGPrefix,runStatePrefix_lift]

theorem initiation_focused (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (mac : HandshakeMac) :
    admitInitiationWith lifted (record ∘ HandshakeCausal.Event.admission) mac =
      HandshakeWorker.old record decode (HandshakeCausal.initiation mac) := by
  unfold HandshakeWorker.old HandshakeCausal.initiation admitInitiation
  rw [focus_native_acceptance, focus_native_acceptance]
  unfold admitInitiationWith
  rw [initiationCheck_lifted,initiationCheck_native]
  rfl

theorem response_focused (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (mac : HandshakeMac) :
    admitResponseWith lifted (record ∘ HandshakeCausal.Event.admission) mac =
      HandshakeWorker.old record decode (HandshakeCausal.response mac) := by
  unfold HandshakeWorker.old HandshakeCausal.response admitResponse
  rw [focus_native_acceptance, focus_native_acceptance]
  unfold admitResponseWith
  rw [responseCheck_lifted,responseCheck_native]
  rfl

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
