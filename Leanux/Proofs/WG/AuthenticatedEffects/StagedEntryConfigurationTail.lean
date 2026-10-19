import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryLifecycleSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySavedSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryFixtureSource

/-! Configuration after peer acquisition and interface opening reuse the
actual staging and counted release contracts. Saved keepalive metadata writes
retain the exact staged and TX queues supplied by their original peer read. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationTail
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
open SourcePassive Driver LifecycleSource
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Checked debts locals Safe (configOut hooks attrs peer ret) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold configOut
  repeat' entry_lifecycle_step Safe using entrySafe

variable (staging : ∀ pid, Checked debts locals Safe (stagingObserved hooks pid))
variable (keepalive : ∀ pid, Checked debts locals Safe (keepaliveObserved hooks pid))
include staging

theorem finish_end (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) (running : Bool) :
    Checked debts locals Safe (do
      if ← liftWGPrefix (branch .peerRunning running) then
        FixtureEffects.runWith (fixtureOps hooks) (.peerConfiguration attrs pid .staging) (stagingObserved hooks pid)
      configOut hooks attrs peer ret) := by
  apply StatePrefixEnsures.bind (SourcePassive.native Safe entrySafe _ (TimerFrames.branch_frame _ _))
  intro active
  cases active with
  | false => exact out Safe entrySafe attrs peer ret
  | true =>
    exact StatePrefixEnsures.bind (FixtureSource.run Safe entrySafe _ _ (staging pid))
      (fun _ => out Safe entrySafe attrs peer ret)

include keepalive

theorem finish (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Checked debts locals Safe (configTailFinish hooks attrs peer pid ret) := by
  unfold configTailFinish FixtureEffects.peerFinishObserved FixtureEffects.peerFinishWith
  apply StatePrefixEnsures.bind (SourcePassive.native Safe entrySafe _ (TimerFrames.store getDev_sameWGStore))
  intro d
  apply StatePrefixEnsures.bind (SourcePassive.native Safe entrySafe _ (TimerFrames.branch_frame _ _))
  intro keep
  cases keep with
  | false => exact finish_end Safe entrySafe staging attrs peer pid ret d.running
  | true =>
    dsimp only
    apply StatePrefixEnsures.bind (SavedSource.read Safe entrySafe pid)
    intro p
    apply StatePrefixEnsures.bind (SavedSource.store Safe entrySafe pid p _
      (Staged.Origins.Native.keepalive_decision p _ d.running))
    intro send
    apply StatePrefixEnsures.bind (SavedSource.write Safe entrySafe pid p
      (fun p => {p with persistentKeepaliveInterval := attrs.keepalive.getD 0}) (fun _ => ⟨rfl,rfl,rfl⟩))
    intro ignored
    apply StatePrefixEnsures.bind (SourcePassive.native Safe entrySafe _ (TimerFrames.branch_frame _ _))
    intro now
    cases now with
    | false => exact finish_end Safe entrySafe staging attrs peer pid ret d.running
    | true =>
      exact StatePrefixEnsures.bind (FixtureSource.run Safe entrySafe _ _ (keepalive pid))
        (fun _ => finish_end Safe entrySafe staging attrs peer pid ret d.running)

macro "entry_config_tail_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_head FixtureEffects.runWith
     apply FixtureSource.run $safe $entry
     change StatePrefixEnsures (Source.Carrier _ _) _ _ (fun _ => Source.Carrier _ _))
  | (maintenance_head liftWGPrefix
     apply SourcePassive.native $safe $entry
     solve
       | (snapshot_head setAllowedip; exact RoutingFrames.set _ _)
       | (snapshot_head removeByPeer; exact RoutingFrames.remove _)
       | (snapshot_head setPeerEndpoint; exact EndpointFrames.set _ _)
       | entry_lifecycle_native)
  | (entry_consumer_update_head
     apply TimerQueue.update_bind $safe $entry
     · intro p; exact ⟨rfl,rfl,rfl⟩
     intro ignored
     change StatePrefixEnsures (Source.Carrier _ _) _ _ (fun _ => Source.Carrier _ _))
  | entry_lifecycle_step $safe using $entry)

theorem tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Checked debts locals Safe (configTail hooks attrs peer pid) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (maintenance_head configOut; exact out Safe entrySafe _ _ _)
    | (maintenance_head configTailFinish; exact finish Safe entrySafe staging keepalive _ _ _ _)
    | entry_config_tail_step Safe using entrySafe

theorem opened : Checked debts locals Safe (openObserved hooks) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold openObserved FixtureEffects.openObserved FixtureEffects.openWith
  repeat' first
    | (maintenance_head stagingObserved; exact staging _)
    | (maintenance_head keepaliveObserved; exact keepalive _)
    | entry_config_tail_step Safe using entrySafe

theorem up : Checked debts locals Safe (upObserved hooks) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold upObserved
  repeat' first
    | (maintenance_head openObserved; exact opened Safe entrySafe staging keepalive)
    | entry_config_tail_step Safe using entrySafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationTail
