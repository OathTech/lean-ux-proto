import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeStaging

/-! Explicit local-operation scopes balance their actual guarded callback.
The root marker appears only at the existing fixture sites in the shared source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
set_option maxHeartbeats 600000

theorem fixture (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α) (safe : StateSafe body) :
    StateSafe (FixtureEffects.runWith (Driver.fixtureOps hooks) trigger body) := by
  change StateSafe (FixtureEffects.runWith (FixtureEffects.scopeHooks Event.scope CausalSources.Cause.fixture) trigger body)
  rw [FixtureEffects.run_scope]
  exact state_scope (.fixture trigger) body safe

theorem fixture_transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (FixtureEffects.runWith (Driver.fixtureOps hooks) (.transmit family addr packets mtu)
      (Driver.transmitObserved hooks family addr packets mtu)) :=
  fixture _ _ (transmit_front _ _ _ _)

theorem interface_open : StateSafe (FixtureEffects.openObserved (Driver.fixtureOps hooks)
    (Driver.stagingObserved hooks) (Driver.keepaliveObserved hooks)) := by
  unfold FixtureEffects.openObserved FixtureEffects.openWith
  repeat' first
    | (scope_balance_head FixtureEffects.runWith; apply fixture)
    | (scope_balance_head Driver.stagingObserved; exact staging _)
    | (scope_balance_head Driver.keepaliveObserved; exact keepalive _)
    | scope_state_step

theorem peer_finish (out : PeerAttrs → Option PeerId → Int → WGPrefix Event Int)
    (safe : ∀ attrs peer ret, StateSafe (out attrs peer ret))
    (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateSafe (FixtureEffects.peerFinishObserved (Driver.fixtureOps hooks)
      (Driver.stagingObserved hooks) (Driver.keepaliveObserved hooks) out attrs peer pid ret) := by
  unfold FixtureEffects.peerFinishObserved FixtureEffects.peerFinishWith
  repeat' first
    | exact safe _ _ _
    | (scope_balance_head FixtureEffects.runWith; apply fixture)
    | (scope_balance_head Driver.stagingObserved; exact staging _)
    | (scope_balance_head Driver.keepaliveObserved; exact keepalive _)
    | scope_state_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
