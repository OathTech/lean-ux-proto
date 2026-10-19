import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteIngressFrames

/-! The actual UDP ingress follows header checks, index lookup, RX allocation,
queue admission and observed peer repayment in source order. RX allocation and
free transport packet bounds; releases retain their counted successor ledger.
Every stopped prefix keeps the enclosing account-safe cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteIngress
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompletePassive NestedPeerRelease Driver
open CompleteCarrier (Accounted)
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem new_rx (pkt : RxPacket) : Checked debts locals Safe (liftWGPrefix (newRxSkb pkt)) := by
  apply StatePrefixEnsures.lift
  · intro h w _ before
    obtain ⟨ledger,accounted⟩ := before
    exact accountSafe ledger h w accounted
  · intro h w a value v b before run
    obtain ⟨ledger,entry,complete⟩ := before
    exact ⟨ledger,(hoare_iff_run_ambient _ _ _).mp (new_rx_entry pkt) w a value v b entry run,complete⟩

open Lean Meta Elab Tactic in
elab "complete_ingress_lift " wanted:ident : tactic => withMainContext do
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

macro "complete_ingress_native" : tactic => `(tactic| (
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  try simp (config := {zeta := false}) only [WG.andM,WG.orM,branch,branchCmp,invariant,unsupported]
  repeat' first
    | (rx_retention_head indexLookup; exact HandshakeLookup.index_lookup _ _ initial)
    | (rx_retention_head keypairGet; exact key_get _ initial)
    | (rx_retention_head keypairGetNull; exact TimerFrames.store keypairGetNull_sameStore initial)
    | (rx_retention_head keypairPut; exact KeyFrames.put _ _ initial)
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact enqueue _ initial)
    | (rx_retention_head RxWorkers.publishSource; exact CompleteDecrypt.publication _ _ initial)
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (fun w => StagedEntry.view w = initial))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (fun w => StagedEntry.view w = initial))
    | (rx_retention_head cpumaskNextOnline; exact next_cpu initial)
    | (rx_retention_head queueDeviceWork; unfold queueDeviceWork; exact hoare_liftAmbient _ _)
    | entry_key_step initial))

macro "complete_ingress_step " safe:term " using " accounted:term : tactic => `(tactic| first
  | (complete_ingress_lift newRxSkb; exact new_rx $safe $accounted _)
  | (complete_ingress_lift freeRxSkb; exact CompletePollNative.free_rx $safe $accounted _)
  | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ $safe $accounted)
  | (maintenance_head liftWGPrefix; apply CompletePassive.native $safe $accounted; solve | complete_ingress_native)
  | (maintenance_head Pure.pure; exact pure_checked $safe $accounted _)
  | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ => CompleteCarrier.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem data (msg : Key) (src : SkbSource) (ds : Nat) :
    Checked debts locals Safe (NestedPeerRelease.ingress (nestedOps hooks) msg src ds) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold NestedPeerRelease.ingress NestedPeerRelease.ingressWith
    NestedPeerRelease.admitWith RxOrigin.admitWith
    NestedPeerRelease.ingressFinishWith RxOrigin.finishWith NestedPeerRelease.publishWith
  simp only [nestedOps,monadLift_self]
  repeat' complete_ingress_step Safe using accountSafe

/-- Every actual UDP ingress branch preserves paired entry and terminal
accounting, including packet allocation, refusal, failed queue admission and
stopped prefixes. Only the explicit enclosing account-safe embedding is used. -/
theorem checked (msg : Key) (src : SkbSource) :
    CompletePoll.Checked debts locals Safe (receiveEntryObserved hooks msg src) := by
  apply CompletePoll.state Safe
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold NestedPeerRelease.receive NestedPeerRelease.receiveWith NestedPeerRelease.packetReceiveWith
  simp only [nestedOps]
  repeat' first
    | (maintenance_head NestedPeerRelease.ingress; exact data Safe accountSafe _ _ _)
    | complete_ingress_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteIngress
