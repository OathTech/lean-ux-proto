import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Leanux.Proofs.WG.Index.SessionOperations
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.SessionEvaluation
open Leanux Leanux.WG Leanux.Proofs.WG.Progress

/-- The actual allocation consumer with no allocation retry loop: at most one
original concrete encounter helper is called. All bypass and error paths remain. -/
def allocationOnce : AmbientM Bool := do
  let entry ← get
  let placeholders := entry.hidden.isNone && entry.hiddenPlaceholders
  if !placeholders && !entry.allocArmed.contains "kzallocKeypair" then return true
  if placeholders then
    (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocPlaceholder) .kzallocKeypair
  else
    (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocRecord) .kzallocKeypair

theorem allocationOnce_source :
    AmbientM.hiddenAlloc .kzallocKeypair = allocationOnce := by
  rw [hiddenAlloc_finite_source]
  unfold hiddenAllocFinite allocationOnce
  simp only [AllocSite.info]
  apply bind_congr
  intro entry
  by_cases bypass : (!(entry.hidden.isNone && entry.hiddenPlaceholders) &&
      !entry.allocArmed.contains "kzallocKeypair") = true
  · simp only [bypass, ite_true]
  · simp only [bypass, Bool.false_eq_true, ite_false, allocationEval, bind_assoc]
    conv =>
      rhs
      rw [← bind_pure (if entry.hidden.isNone && entry.hiddenPlaceholders then
        (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocPlaceholder) .kzallocKeypair
        else (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocRecord) .kzallocKeypair)]
    apply bind_congr
    intro ok
    cases ok <;> rfl

/-- Same complete allocation/store operation, with the unique encounter reduced. -/
def createFinite (peer : Option PeerId) : WG.M (Option KeypairId) := do
  let ok ← monadLift allocationOnce
  if ← branch .keypairCreateNoMem !ok then return none
  let internalId := (← get).keypairCounter + 1
  modify fun k => {k with keypairCounter := internalId}
  let id := (← getDev).nextKeypairId
  modifyDev fun d => {d with nextKeypairId := id + 1}
  setKeypair id {internalId, peer}
  return some id

theorem createFinite_source (peer : Option PeerId) :
    keypairCreate peer = createFinite peer := by
  unfold keypairCreate createFinite
  have source : (hiddenAlloc .kzallocKeypair : WG.M Bool) =
      monadLift allocationOnce := by
    change monadLift (AmbientM.hiddenAlloc .kzallocKeypair) = _
    rw [allocationOnce_source]
  rw [source]

/-- Complete original session evaluator with the only nonstructural loop
replaced by its actual zero-or-one concrete encounter. The suffix is the
original fixed sequence; it is not an arbitrary callback. -/
def evaluate (pid : PeerId) : WG.M Bool := do
  let st := (← getPeer pid).handshakeState
  if ← WG.andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
      (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE)) then return false
  let created ← createFinite (← IndexOwner.peerWord (.handshake pid))
  Index.sessionAfterCreate pid st created

theorem evaluate_source (pid : PeerId) : beginSession pid = evaluate pid := by
  rw [Index.beginSession_owner_source]
  unfold evaluate
  simp only [createFinite_source]

end Leanux.Proofs.WG.Noise.SessionEvaluation
