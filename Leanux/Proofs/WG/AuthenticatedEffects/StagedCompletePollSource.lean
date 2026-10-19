import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteStackSource

/-! The actual nested-release NAPI poll composes native queue bookkeeping,
replay/candidate receipts, receive consumption and tagged GRO callbacks on
one paired ledger. Only its true staging and transmit source contracts are
inputs; all release and native packet-deletion arms are discharged here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePollSource
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal CompletePoll
open CompleteCarrier (Accounted)
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open Lean Meta Elab Tactic in
elab "complete_poll_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  let action ← if target.isAppOf ``CompletePoll.Checked then
      match args.back? with
      | some action => pure action
      | none => throwError "missing action"
    else if target.isAppOf ``PrefixEnsures then
      match args[args.size - 2]? with
      | some action => pure action
      | none => throwError "missing prefix action"
    else throwError "not a paired product contract"
  let action := action.consumeMData.headBeta
  let action ← if action.isAppOf ``liftWGObserver then
      match action.getAppArgs.back? with
      | some body => pure body.consumeMData
      | none => throwError "missing WireGuard observer body"
    else pure action
  let .const actual _ := action.getAppFn | throwError "not a constant source head"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

open Lean Meta Elab Tactic in
elab "complete_poll_leaf " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  let action ← if target.isAppOf ``CompletePoll.Checked then
      match args.back? with
      | some action => pure action
      | none => throwError "missing action"
    else if target.isAppOf ``PrefixEnsures then
      match args[args.size - 2]? with
      | some action => pure action
      | none => throwError "missing prefix action"
    else throwError "not a paired product contract"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``liftWGObserver do throwError "not a WG observer"
  let some body := action.getAppArgs.back? | throwError "missing WG body"
  let body := body.consumeMData.headBeta
  unless body.isAppOf ``liftWGPrefix do throwError "not a native WG lift"
  let some native := body.getAppArgs.back? | throwError "missing native action"
  let .const actual _ := native.consumeMData.headBeta.getAppFn | throwError "not a native constant"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different native head"

macro "complete_poll_native " safe:term " using " accounted:term : tactic => `(tactic| (
  apply CompletePoll.state $safe
  apply CompletePassive.native $safe $accounted
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  try rw [getPeer_twice]
  try unfold WG.andM
  try simp (config := {zeta := false}) only [branch,endpointFromSkb,invariant,unsupported]
  repeat' first
    | (rx_retention_head PrevQueue.peek; exact (TimerFrames.store (prevQueuePeek_sameWGStore _)).wp (· = initial))
    | (rx_retention_head getRxSkb; exact (CompletePollNative.get_rx _).wp (· = initial))
    | (rx_retention_head keypairPut; exact (KeyFrames.put _ _).wp (· = initial))
    | entry_key_step initial))

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
variable (staging : ∀ pid, CompletePassive.Checked debts locals Safe (Driver.stagingObserved hooks pid))
variable (transmit : ∀ family addr packets mtu, CompletePassive.Checked debts locals Safe
  (Driver.transmitObserved hooks family addr packets mtu))
include accountSafe staging transmit

/-- The original occurrence-tagged native poll preserves paired ticket
accounting across every branch, including before later Stop. The real stack
transmit and confirmation-triggered staging contracts remain explicit. -/
theorem native_poll (pid : PeerId) (budget : Nat) : Checked debts locals Safe
    (Driver.nativePollObserved hooks pid budget) := by
  unfold Driver.nativePollObserved NestedPeerRelease.pollWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (complete_poll_head Driver.Hooks.peerRelease; exact CompletePoll.state Safe (CompleteSource.original _ Safe accountSafe))
    | (complete_poll_head Driver.Hooks.candidateEnter; exact CompletePoll.candidate Safe accountSafe _ _)
    | (complete_poll_head Driver.Hooks.candidateLeave; exact CompletePoll.leave Safe accountSafe _)
    | (complete_poll_head Driver.Hooks.counterCheck; exact CompletePoll.counter Safe accountSafe _ _)
    | (complete_poll_head Driver.consumeObserved; exact CompletePoll.state Safe
        (CompleteReceiveConsumer.checked Safe accountSafe _ _ _ (staging _)))
    | (complete_poll_head GroOccurrence.receiveWith; exact CompleteStack.receive Safe accountSafe transmit _ _)
    | (complete_poll_head GroOccurrence.flushAllWith; exact CompleteStack.flush Safe accountSafe transmit _)
    | (complete_poll_leaf freeRxSkb; exact CompletePoll.state Safe (CompletePollNative.free_rx Safe accountSafe _))
    | (complete_poll_head liftWGPrefix; solve | complete_poll_native Safe using accountSafe)
    | (complete_poll_head Pure.pure; exact CompletePoll.pure_checked Safe accountSafe _)
    | (complete_poll_head Bind.bind; apply CompletePoll.bind_checked Safe)
    | (complete_poll_head ite; apply PrefixEnsures.ite)
    | (complete_poll_head ForIn.forIn; apply CompletePoll.list Safe accountSafe)
    | maintenance_intro
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePollSource
