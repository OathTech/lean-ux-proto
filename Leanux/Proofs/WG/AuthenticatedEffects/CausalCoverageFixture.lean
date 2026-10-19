import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageEffects

/-! Only the actual guarded fixture source sites establish local-operation
contexts. Effectful callbacks need a live scope even when their caller is a
configuration or interface-open operation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
set_option maxHeartbeats 600000

theorem fixture (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α) (safe : StateGuarded body) :
    StateAt frames (FixtureEffects.runWith (Driver.fixtureOps hooks) trigger body) := by
  change StateAt frames (FixtureEffects.runWith (FixtureEffects.scopeHooks Event.scope CausalSources.Cause.fixture) trigger body)
  rw [FixtureEffects.run_scope]
  exact state_scope (.fixture trigger) body safe frames

theorem fixture_transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateAt frames (FixtureEffects.runWith (Driver.fixtureOps hooks) (.transmit family addr packets mtu)
      (Driver.transmitObserved hooks family addr packets mtu)) :=
  fixture _ _ (fun _ live => transmit_front _ _ _ _ live)

theorem interface_open : StateAt frames (FixtureEffects.openObserved (Driver.fixtureOps hooks)
    (Driver.stagingObserved hooks) (Driver.keepaliveObserved hooks)) := by
  unfold FixtureEffects.openObserved FixtureEffects.openWith
  repeat' first
    | (coverage_head FixtureEffects.runWith; apply fixture; intro frames live)
    | (coverage_head Driver.stagingObserved; exact staging _ (by assumption))
    | (coverage_head Driver.keepaliveObserved; exact keepalive _ (by assumption))
    | coverage_state_step

theorem peer_finish (out : PeerAttrs → Option PeerId → Int → WGPrefix Event Int)
    (safe : ∀ attrs peer ret, StateClosed (out attrs peer ret))
    (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateAt frames (FixtureEffects.peerFinishObserved (Driver.fixtureOps hooks)
      (Driver.stagingObserved hooks) (Driver.keepaliveObserved hooks) out attrs peer pid ret) := by
  unfold FixtureEffects.peerFinishObserved FixtureEffects.peerFinishWith
  repeat' first
    | exact safe _ _ _ _
    | (coverage_head FixtureEffects.runWith; apply fixture; intro frames live)
    | (coverage_head Driver.stagingObserved; exact staging _ (by assumption))
    | (coverage_head Driver.keepaliveObserved; exact keepalive _ (by assumption))
    | coverage_state_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
