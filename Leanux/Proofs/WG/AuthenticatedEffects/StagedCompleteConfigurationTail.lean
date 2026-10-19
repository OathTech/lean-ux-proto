import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryLifecycleSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSavedSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFixtureSource

/-! Configuration and opening preserve both accounting directions on one ledger.
Saved metadata writes retain exact peer fields; each counted release carries
its own paired successor rather than an assumed quiet history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConfigurationTail
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
open CompletePassive Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem list {α β : Type} (xs : List α) (initial : β) (body : α → β → WGPrefix Event (ForInStep β))
    (checked : ∀ item acc, StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe
      (body item acc) (fun _ => CompleteCarrier.Carrier debts locals)) :
    Checked debts locals Safe (forIn xs initial body) :=
  StatePrefixEnsures.forInInvariant xs initial body (fun _ => CompleteCarrier.Carrier debts locals) Safe
    (fun _ h w _ before => by obtain ⟨ledger,entry⟩ := before; exact accountSafe ledger h w entry) checked

macro "complete_config_base_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_head Hooks.peerRelease; exact CompleteSource.original _ $safe $entry)
  | (maintenance_head Hooks.stagedPurge; exact CompleteSource.purge _ $safe $entry)
  | (maintenance_head liftWGPrefix; apply CompletePassive.native $safe $entry; solve | entry_lifecycle_native)
  | (maintenance_head ForIn.forIn; apply list $safe $entry)
  | (maintenance_head Pure.pure; exact pure_checked $safe $entry _)
  | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ => CompleteCarrier.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Checked debts locals Safe (configOut hooks attrs peer ret) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold configOut
  repeat' complete_config_base_step Safe using accountSafe

variable (staging : ∀ pid, Checked debts locals Safe (stagingObserved hooks pid))
variable (keepalive : ∀ pid, Checked debts locals Safe (keepaliveObserved hooks pid))
include staging

theorem finish_end (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) (running : Bool) :
    Checked debts locals Safe (do
      if ← liftWGPrefix (branch .peerRunning running) then
        FixtureEffects.runWith (fixtureOps hooks) (.peerConfiguration attrs pid .staging) (stagingObserved hooks pid)
      configOut hooks attrs peer ret) := by
  apply StatePrefixEnsures.bind (CompletePassive.native Safe accountSafe _ (TimerFrames.branch_frame _ _))
  intro active
  cases active with
  | false => exact out Safe accountSafe attrs peer ret
  | true =>
    exact StatePrefixEnsures.bind (CompleteFixture.run Safe accountSafe _ _ (staging pid))
      (fun _ => out Safe accountSafe attrs peer ret)

include keepalive

theorem finish (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Checked debts locals Safe (configTailFinish hooks attrs peer pid ret) := by
  unfold configTailFinish FixtureEffects.peerFinishObserved FixtureEffects.peerFinishWith
  apply StatePrefixEnsures.bind (CompletePassive.native Safe accountSafe _ (TimerFrames.store getDev_sameWGStore))
  intro d
  apply StatePrefixEnsures.bind (CompletePassive.native Safe accountSafe _ (TimerFrames.branch_frame _ _))
  intro keep
  cases keep with
  | false => exact finish_end Safe accountSafe staging attrs peer pid ret d.running
  | true =>
    dsimp only
    apply StatePrefixEnsures.bind (CompleteSaved.read Safe accountSafe pid)
    intro p
    apply StatePrefixEnsures.bind (CompleteSaved.store Safe accountSafe pid p _
      (Staged.Origins.Native.keepalive_decision p _ d.running))
    intro send
    apply StatePrefixEnsures.bind (CompleteSaved.write Safe accountSafe pid p
      (fun p => {p with persistentKeepaliveInterval := attrs.keepalive.getD 0}) (fun _ => ⟨rfl,rfl,rfl⟩))
    intro ignored
    apply StatePrefixEnsures.bind (CompletePassive.native Safe accountSafe _ (TimerFrames.branch_frame _ _))
    intro now
    cases now with
    | false => exact finish_end Safe accountSafe staging attrs peer pid ret d.running
    | true =>
      exact StatePrefixEnsures.bind (CompleteFixture.run Safe accountSafe _ _ (keepalive pid))
        (fun _ => finish_end Safe accountSafe staging attrs peer pid ret d.running)

macro "complete_config_tail_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_head FixtureEffects.runWith
     apply CompleteFixture.run $safe $entry
     change StatePrefixEnsures (CompleteCarrier.Carrier _ _) _ _ (fun _ => CompleteCarrier.Carrier _ _))
  | (maintenance_head liftWGPrefix
     apply CompletePassive.native $safe $entry
     solve
       | (snapshot_head setAllowedip; exact RoutingFrames.set _ _)
       | (snapshot_head removeByPeer; exact RoutingFrames.remove _)
       | (snapshot_head setPeerEndpoint; exact EndpointFrames.set _ _)
       | entry_lifecycle_native)
  | (entry_consumer_update_head
     apply CompletePassive.update_bind $safe $entry
     · intro p; exact ⟨rfl,rfl,rfl⟩
     intro ignored
     change StatePrefixEnsures (CompleteCarrier.Carrier _ _) _ _ (fun _ => CompleteCarrier.Carrier _ _))
  | complete_config_base_step $safe using $entry)

theorem tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Checked debts locals Safe (configTail hooks attrs peer pid) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (maintenance_head configOut; exact out Safe accountSafe _ _ _)
    | (maintenance_head configTailFinish; exact finish Safe accountSafe staging keepalive _ _ _ _)
    | complete_config_tail_step Safe using accountSafe

theorem opened : Checked debts locals Safe (openObserved hooks) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold openObserved FixtureEffects.openObserved FixtureEffects.openWith
  repeat' first
    | (maintenance_head stagingObserved; exact staging _)
    | (maintenance_head keepaliveObserved; exact keepalive _)
    | complete_config_tail_step Safe using accountSafe

theorem up : Checked debts locals Safe (upObserved hooks) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold upObserved
  repeat' first
    | (maintenance_head openObserved; exact opened Safe accountSafe staging keepalive)
    | complete_config_tail_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConfigurationTail
