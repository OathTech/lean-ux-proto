import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixPassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalCounted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteIngressSource

/-! The actual UDP ingress follows header checks, index lookup, RX allocation,
queue admission and observed peer repayment in source order. RX allocation and
free transport packet bounds; releases retain their counted successor ledger.
All logical journal prefixes are retained, including stopped executions.
Native interval correspondence remains separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Ingress
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
open NestedPeerRelease Driver
open CompleteIngress
open CompleteCarrier (Accounted)
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem new_rx (pkt : RxPacket) : Checked debts locals Safe (liftWGPrefix (newRxSkb pkt)) :=
  StateEnsures.quiet (CompleteIngress.new_rx Safe accountSafe pkt) (fun _ _ _=>rfl)

include accountSafe in
theorem free_rx (skb : SkbId) : Checked debts locals Safe (liftWGPrefix (freeRxSkb skb)) :=
  StateEnsures.quiet (CompletePollNative.free_rx Safe accountSafe skb) (fun _ _ _=>rfl)

open Lean Meta Elab Tactic in
elab "prefix_ingress_lift " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do throwError "not an observer contract"
  let body := args[args.size - 2]!.consumeMData.headBeta
  unless body.isAppOf ``liftWGPrefix do throwError "not a WG lift"
  let native := body.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a constant native action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different native action"

macro "prefix_ingress_step " safe:term " using " accounted:term : tactic => `(tactic| first
  | (prefix_ingress_lift newRxSkb; exact new_rx $safe $accounted _)
  | (prefix_ingress_lift freeRxSkb; exact free_rx $safe $accounted _)
  | (maintenance_head Hooks.peerRelease; exact Disposal.original _ $safe $accounted)
  | (maintenance_head liftWGPrefix; apply Passive.native $safe $accounted; solve | complete_ingress_native)
  | (maintenance_head Pure.pure; exact pure_checked $safe $accounted _)
  | (maintenance_head Bind.bind; apply StateEnsures.bind (Q := fun _ => CompleteCarrier.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem data (msg : Key) (src : SkbSource) (ds : Nat) :
    Checked debts locals Safe (NestedPeerRelease.ingress (nestedOps hooks) msg src ds) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold NestedPeerRelease.ingress NestedPeerRelease.ingressWith
    NestedPeerRelease.admitWith RxOrigin.admitWith
    NestedPeerRelease.ingressFinishWith RxOrigin.finishWith NestedPeerRelease.publishWith
  simp only [nestedOps,monadLift_self]
  repeat' prefix_ingress_step Safe using accountSafe

/-- Every actual UDP ingress branch preserves paired entry and terminal
accounting, including packet allocation, refusal, failed queue admission and
stopped prefixes. Only the explicit enclosing account-safe embedding is used. -/
theorem checked (msg : Key) (src : SkbSource) :
    Ensures (CompletePoll.Carrier debts locals) Safe (receiveEntryObserved hooks msg src)
      (fun _=>CompletePoll.Carrier debts locals) := by
  apply StateEnsures.liftWG
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold NestedPeerRelease.receive NestedPeerRelease.receiveWith NestedPeerRelease.packetReceiveWith
  simp only [nestedOps]
  repeat' first
    | (maintenance_head NestedPeerRelease.ingress; exact data Safe accountSafe _ _ _)
    | prefix_ingress_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Ingress
