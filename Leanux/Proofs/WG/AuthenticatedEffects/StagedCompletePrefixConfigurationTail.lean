import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixLifecycleSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixConfigurationSaved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixConfigurationFixture

/-! Configuration and opening preserve both accounting directions on one ledger.
Saved metadata writes retain exact peer fields; each counted release carries
its own paired successor rather than an assumed quiet history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationTail
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
open Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

omit accountSafe in
theorem list {α β : Type} (xs : List α) (initial : β) (body : α→β→WGPrefix Event (ForInStep β))
    (checked : ∀ item acc, StateEnsures (CompleteCarrier.Carrier debts locals) Safe
      (body item acc) (fun _=>CompleteCarrier.Carrier debts locals)) :
    Checked debts locals Safe (forIn xs initial body) :=
  StateEnsures.forIn xs initial body (fun _=>CompleteCarrier.Carrier debts locals) checked

macro "prefix_config_base_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_head Hooks.peerRelease; exact Disposal.original _ $safe $entry)
  | (maintenance_head Hooks.stagedPurge; exact Disposal.purge _ $safe $entry)
  | (maintenance_head liftWGPrefix; apply Passive.native $safe $entry; solve | entry_lifecycle_native)
  | (maintenance_head ForIn.forIn; apply list $safe)
  | (maintenance_head Pure.pure; exact pure_checked $safe $entry _)
  | (maintenance_head Bind.bind; apply StateEnsures.bind (Q := fun _ => CompleteCarrier.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Checked debts locals Safe (configOut hooks attrs peer ret) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold configOut
  repeat' prefix_config_base_step Safe using accountSafe

variable (staging : ∀ pid, Checked debts locals Safe (stagingObserved hooks pid))
variable (keepalive : ∀ pid, Checked debts locals Safe (keepaliveObserved hooks pid))
include staging

theorem finish_end (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) (running : Bool) :
    Checked debts locals Safe (do
      if ← liftWGPrefix (branch .peerRunning running) then
        FixtureEffects.runWith (fixtureOps hooks) (.peerConfiguration attrs pid .staging) (stagingObserved hooks pid)
      configOut hooks attrs peer ret) := by
  apply StateEnsures.bind (Passive.native Safe accountSafe _ (TimerFrames.branch_frame _ _))
  intro active
  cases active with
  | false => exact out Safe accountSafe attrs peer ret
  | true =>
    exact StateEnsures.bind (ConfigurationFixture.run Safe accountSafe _ _ (staging pid))
      (fun _ => out Safe accountSafe attrs peer ret)

include keepalive

theorem finish (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Checked debts locals Safe (configTailFinish hooks attrs peer pid ret) := by
  unfold configTailFinish FixtureEffects.peerFinishObserved FixtureEffects.peerFinishWith
  apply StateEnsures.bind (Passive.native Safe accountSafe _ (TimerFrames.store getDev_sameWGStore))
  intro d
  apply StateEnsures.bind (Passive.native Safe accountSafe _ (TimerFrames.branch_frame _ _))
  intro keep
  cases keep with
  | false => exact finish_end Safe accountSafe staging attrs peer pid ret d.running
  | true =>
    dsimp only
    apply StateEnsures.bind (ConfigurationSaved.read Safe accountSafe pid)
    intro p
    apply StateEnsures.bind (ConfigurationSaved.store Safe accountSafe pid p _
      (Staged.Origins.Native.keepalive_decision p _ d.running))
    intro send
    apply StateEnsures.bind (ConfigurationSaved.write Safe accountSafe pid p
      (fun p => {p with persistentKeepaliveInterval := attrs.keepalive.getD 0}) (fun _ => ⟨rfl,rfl,rfl⟩))
    intro ignored
    apply StateEnsures.bind (Passive.native Safe accountSafe _ (TimerFrames.branch_frame _ _))
    intro now
    cases now with
    | false => exact finish_end Safe accountSafe staging attrs peer pid ret d.running
    | true =>
      exact StateEnsures.bind (ConfigurationFixture.run Safe accountSafe _ _ (keepalive pid))
        (fun _ => finish_end Safe accountSafe staging attrs peer pid ret d.running)

macro "prefix_config_tail_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_head FixtureEffects.runWith
     apply ConfigurationFixture.run $safe $entry
     change StateEnsures (CompleteCarrier.Carrier _ _) _ _ (fun _ => CompleteCarrier.Carrier _ _))
  | (maintenance_head liftWGPrefix
     apply Passive.native $safe $entry
     solve
       | (snapshot_head setAllowedip; exact RoutingFrames.set _ _)
       | (snapshot_head removeByPeer; exact RoutingFrames.remove _)
       | (snapshot_head setPeerEndpoint; exact EndpointFrames.set _ _)
       | entry_lifecycle_native)
  | (entry_consumer_update_head
     apply Passive.update_bind $safe $entry
     · intro p; exact ⟨rfl,rfl,rfl⟩
     intro ignored
     change StateEnsures (CompleteCarrier.Carrier _ _) _ _ (fun _ => CompleteCarrier.Carrier _ _))
  | prefix_config_base_step $safe using $entry)

theorem tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Checked debts locals Safe (configTail hooks attrs peer pid) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (maintenance_head configOut; exact out Safe accountSafe _ _ _)
    | (maintenance_head configTailFinish; exact finish Safe accountSafe staging keepalive _ _ _ _)
    | prefix_config_tail_step Safe using accountSafe

theorem opened : Checked debts locals Safe (openObserved hooks) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold openObserved FixtureEffects.openObserved FixtureEffects.openWith
  repeat' first
    | (maintenance_head stagingObserved; exact staging _)
    | (maintenance_head keepaliveObserved; exact keepalive _)
    | prefix_config_tail_step Safe using accountSafe

theorem up : Checked debts locals Safe (upObserved hooks) := by
  change StateEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold upObserved
  repeat' first
    | (maintenance_head openObserved; exact opened Safe accountSafe staging keepalive)
    | prefix_config_tail_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationTail
