import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionLifecycle
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionDeferredBase
import Leanux.Proofs.WG.TransmitSecurity.DriverLifecycleHistory

/-! Configuration, removal and lifecycle callbacks preserve both live append
accounting and previously recorded delivery certificates on the same run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem config_device (attrs : DeviceAttrs) : StateSafe (Driver.configDevice hooks attrs) :=
  state_combine _ (Emissions.config_device attrs)
    (Driver.configDevice_history (g := quietHooks) quiet_hooks.actors attrs)

theorem up : StateSafe (Driver.upObserved hooks) :=
  state_combine _ Emissions.up (Driver.up_history (g := quietHooks) quiet_hooks.actors)

theorem down : StateSafe (Driver.downObserved hooks) :=
  state_combine _ Emissions.down (Driver.down_history (g := quietHooks) quiet_hooks.actors)

theorem destruct : StateSafe (Driver.destructObserved hooks) :=
  state_combine _ Emissions.destruct (Driver.destruct_history (g := quietHooks) quiet_hooks.actors)

theorem device_create : StateSafe (liftWGPrefix wgCreate) :=
  state_native _ Emissions.device_create

theorem fixture (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α) (safe : StateSafe body) :
    StateSafe (FixtureEffects.runWith (Driver.fixtureOps hooks) trigger body) := by
  unfold FixtureEffects.runWith
  apply state_bind
  · apply state_combine _ _ (quiet_hooks.fixtureEnter trigger)
    intro w a h hi
    exact ⟨[.scope (.entered ⟨h.length,.fixture trigger⟩)],rfl,True.intro,hi.quiet _ rfl⟩
  · intro token
    exact state_bind safe (fun value => state_bind
      (state_combine _ (Emissions.state_emit _ rfl) (quiet_hooks.fixtureLeave token))
      (fun _ => state_pure value))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
