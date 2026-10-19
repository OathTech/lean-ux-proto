import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConsumerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourcePassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerQueue

/-! Actual handshake and cookie checking paths compose their native frames
with counted nested repayment. The source keeps all pre-acceptance effects
and Stop prefixes; no generic native action or release contract is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConsumerSource
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open SourcePassive NestedPeerRelease
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

abbrev nested := NestedPeerRelease.observedOps Event.stagedDisposal stagedDisposal?

open Lean Meta Elab Tactic in
elab "entry_consumer_update_head" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do throwError "not an observer contract"
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not an observer bind"
  let bindArgs := action.getAppArgs
  unless bindArgs.size ≥ 2 do throwError "missing bind arguments"
  let head := bindArgs[bindArgs.size - 2]!.consumeMData
  unless head.isAppOf ``liftWGPrefix do throwError "not a native lift"
  unless head.getAppArgs.back!.consumeMData.isAppOf ``getPeer do throwError "not a peer read"
  let .lam _ _ body _ := bindArgs.back!.consumeMData | throwError "not an explicit continuation"
  unless body.consumeMData.isAppOf ``Bind.bind do throwError "not a write continuation"
  let nextArgs := body.consumeMData.getAppArgs
  unless nextArgs.size ≥ 2 do throwError "missing write arguments"
  let next := nextArgs[nextArgs.size - 2]!.consumeMData
  unless next.isAppOf ``liftWGPrefix do throwError "not a native write lift"
  unless next.getAppArgs.back!.consumeMData.isAppOf ``setPeer do throwError "not a peer write"

macro "entry_consumer_source " safe:term " using " entry:term : tactic => `(tactic| first
  | (entry_consumer_update_head
     apply TimerQueue.update_bind $safe $entry
     · intro p; exact ⟨rfl,rfl,rfl⟩
     intro ignored
     change StatePrefixEnsures (Source.Carrier _ _) _ _ (fun _ => Source.Carrier _ _))
  | (maintenance_head liftWGPrefix; apply SourcePassive.native $safe $entry; solve | entry_consumer_native)
  | (maintenance_head HandshakeSecurity.StagedDisposal.Decoration.release; exact Source.release _ $safe $entry)
  | (maintenance_head Pure.pure; exact pure_checked $safe $entry _)
  | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ => Source.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem initiation_check (msg : Key) : Checked debts locals Safe (initiationCheckWith nested msg) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold initiationCheckWith initiationTailWith initiationOutWith
  simp only [nested,observedOps]
  repeat' entry_consumer_source Safe using entrySafe

theorem response_check (msg : Key) : Checked debts locals Safe (responseCheckWith nested msg) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold responseCheckWith responseTailWith
  simp only [nested,observedOps]
  repeat' entry_consumer_source Safe using entrySafe

theorem cookie (msg : Key) : Checked debts locals Safe (cookieWith nested msg) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold cookieWith cookieAfterWith
  simp only [nested,observedOps]
  repeat' entry_consumer_source Safe using entrySafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConsumerSource
