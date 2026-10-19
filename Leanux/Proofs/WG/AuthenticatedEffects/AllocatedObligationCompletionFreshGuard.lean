import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFreshQueued

/-! The rekey guard is the original ordered native read/choice prefix. Its
frame includes the complete indexed entry view, not just allocated cells. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open LifetimeEffects

def guardNative (pid : PeerId) : WG.M Bool := do
  let current := (← getPeer pid).keypairCurrent
  let send ← andPrefix (branch .freshKeypair current.isSome) do
    let some id := current | invariant "unreachable"
    let k ← getKeypair id
    andPrefix (branch .freshValid k.sending.isValid) do
      orPrefix (branchCmp .freshCounter (k.sendingCounter > REKEY_AFTER_MESSAGES) k.sendingCounter REKEY_AFTER_MESSAGES) do
        andPrefix (branch .freshInitiator k.iAmTheInitiator) do
          branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME
  branch .freshSend send

theorem guard_lifted (pid : PeerId) :
    guardWith (RawAppend.lifetimeLifted : Ops (WGPrefix E)) pid = liftWGPrefix (guardNative pid) := by
  unfold guardWith guardNative
  simp only [andPrefix,orPrefix,RawAppend.lifetimeLifted,StagedEntry.Queued.lift_bind,bind_assoc]
  repeat' first
    | rfl
    | (apply StagedEntry.Queued.bind_same; intro value)
    | (simp only [StagedEntry.Queued.lift_bind,StagedEntry.Queued.lift_if,
        StagedEntry.Queued.lift_pure,bind_assoc])
    | split
  all_goals simp_all

theorem guard_original (pid : PeerId) : StateProjectsPrefix ledgerEvent? id
    (guardWith CausalJournal.completionLifetime pid) (liftWGPrefix (guardNative pid)) := by
  rw [guard_actual,← guard_lifted]
  exact guard_projects ledgerEvent? prefix_projects pid

theorem key_read_view (kid : KeypairId) : SameView StagedEntry.view (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a key v b run
  exact congrArg StagedEntry.view (KeyTimes.getKeypair_return kid w v key a b run).1

theorem guard_views (pid : PeerId) : SameView StagedEntry.view (guardNative pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold guardNative
  simp only [andPrefix,orPrefix,branch,branchCmp]
  repeat' first
    | (rx_retention_head getKeypair; exact (key_read_view _).wp (· = initial))
    | (rx_retention_head invariant; unfold invariant; exact hoare_liftAmbient _ _)
    | queued_entry_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
