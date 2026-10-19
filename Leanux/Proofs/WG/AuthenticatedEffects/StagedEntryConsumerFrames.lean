import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeLookup
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeyFrames
import Leanux.Proofs.WG.AuthenticatedEffects.InitiationFront

/-! The accepted consumer suffix writes handshake metadata only. Rejected
consumer repayment is deliberately left to its actual source observer. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConsumerFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
open Queues.RxCredits.HandshakeLoans
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem initiation_front (msg : Key) : SameView StagedEntry.view (initiationAuthFront msg) :=
  (initiationAuthFront_same_world msg).factor StagedEntry.view

theorem cookie_front (msg : Key) (pid : PeerId) : SameView StagedEntry.view (cookieAuthFront msg pid) :=
  (cookieAuthFront_same_world msg pid).factor StagedEntry.view

theorem out_some (peer : Option PeerId) (pid : PeerId) :
    SameView StagedEntry.view (initiationOut peer (some pid)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  change Except.ok ((some pid,w),CounterWindow.record a .consumeFailedPut false) = _ at run
  cases run
  rfl

theorem initiation_finish (msg : Key) (accepted : AcceptedInitiation) :
    SameView StagedEntry.view (initiationAcceptedFinish msg accepted) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold initiationAcceptedFinish
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64]
  repeat' first
    | (rx_retention_head initiationOut; exact (out_some _ _).wp (· = initial))
    | entry_key_step initial

theorem response_finish (msg : Key) (accepted : AcceptedResponse) :
    SameView StagedEntry.view (responseAcceptedFinish msg accepted) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold responseAcceptedFinish
  repeat' entry_key_step initial

theorem initiation_continue (msg : Key) (accepted : Option AcceptedInitiation) :
    SameView StagedEntry.view (initiationAcceptedContinue msg accepted) := by
  cases accepted with
  | none => exact SameView.pure _ _
  | some accepted => exact initiation_finish msg accepted

theorem response_continue (msg : Key) (accepted : Option AcceptedResponse) :
    SameView StagedEntry.view (responseAcceptedContinue msg accepted) := by
  cases accepted with
  | none => exact SameView.pure _ _
  | some accepted => exact response_finish msg accepted

macro "entry_consumer_native" : tactic => `(tactic| (
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  try simp (config := {zeta := false}) only [WG.andM,WG.orM,branch,branchCmp,hiddenClock64]
  repeat' first
    | (rx_retention_head initiationAuthFront; exact initiation_front _ initial)
    | (rx_retention_head cookieAuthFront; exact cookie_front _ _ initial)
    | (rx_retention_head pubkeyLookup; exact HandshakeLookup.public_lookup _ initial)
    | (rx_retention_head indexLookup; exact HandshakeLookup.index_lookup _ _ initial)
    | entry_key_step initial))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConsumerFrames
