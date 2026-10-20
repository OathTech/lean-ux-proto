import Leanux.Proofs.WG.Progress.RunnerBoundarySource
import Leanux.Proofs.WG.Progress.SeccompPrefillFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RunnerFinite
open Leanux Leanux.Runner

/-- Initialization with only its prefill translation dependency exposed.
The fixture tables and finite boot sequence remain the original ones. -/
def initialWith (prefill : Nat → SeccompWorld → TaskWorld → Except String (SeccompWorld × TaskWorld))
    (trace : Trace) (placeholders : Bool) : Except (Nat × Stop) World := do
  let ambient : Ambient := { env := harnessEnv, timing := Env.timing,
                             allocArmed := trace.allocArmed,
                             hiddenPlaceholders := placeholders && trace.hidden.isNone,
                             steerValues := if placeholders then trace.steer else [],
                             armRecords := trace.armRecords,
                             allocSteered := if placeholders then
                               (trace.steer.map (·.1)).filter fun l => AllocSite.all.any (·.info.label == l)
                             else [] }
  let mut world : World := { ambient,
                             fs := initialFS trace.net trace.foreign trace.stepped trace.seccompChild,
                             tasks := initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild,
                             wg := { initialWG trace.net trace.bare with
                                     portBound := Env.portBound,
                                     fixtureNetDevices := Env.fixtureNetDevices,
                                     dstCacheRecords := trace.dstCacheRecords,
                                     routing := { foreignCreator := trace.foreign } },
                             fixture := { netnsCHolders := if trace.foreign then [9, 8, 5, 4] else [],
                                          routes := trace.routes,
                                          napiBeforePut := trace.napiBeforePut } }
  -- the seccomp prefill fixture (design 5): the chain the guest installed before the window
  if trace.seccompPrefill > 0 then
    match prefill trace.seccompPrefill world.seccomp world.tasks with
    | .ok (seccomp, tasks) => world := { world with seccomp, tasks }
    | .error e => throw (0, .invariant e)
  -- lane C: the fixture namespaces' IPv4 tables at boot (`lo` up in each),
  -- built by the C's own sequence outside every window (the design note,
  -- 9.3); its steps are discarded with the first operation's reset
  if trace.net then
    let boot : M Unit := do
      Net.Fib.bootTables
      if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables
    match boot.run world with
    | .ok (_, w) => world := { w with ambient := { w.ambient with steps := #[], envCalls := [] } }
    | .error e => throw (0, e)
  return world

theorem initial_factor (trace : Trace) (placeholders : Bool) :
    runnerInitial trace placeholders = initialWith Env.seccompPrefill trace placeholders := rfl

def initial := initialWith SeccompPrefillFinite.install

theorem initial_source (trace : Trace) (placeholders : Bool) :
    runnerInitial trace placeholders = initial trace placeholders := by
  rw [initial_factor]
  change initialWith Seccomp.Prefill.apply trace placeholders = _
  rw [SeccompPrefillFinite.install_source]
  rfl

end Leanux.Proofs.WG.Progress.RunnerFinite
