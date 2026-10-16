import Leanux.Proofs.WG.Lifetimes.BatchTrials

/-! The concrete Batch scheduler family retains original result types. Its
contract is resolved-current-store access safety, separate from saved-reference
ownership, lifecycle closure and termination without an original Stop. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.Proofs.Logged

inductive BatchCall where
  | napi
  | irqExit
  | hasWork (a : Activation)
  | occupancy (a : Activation)
  | cryptAhead (pid : WG.PeerId)
  | iteration (a : Activation)
  | activation (a : Activation)
  | dispatch (worker : Worker)
  | schedule (stack : Option Worker)
  | nestedResched (worker : Worker)

namespace BatchCall

def Result : BatchCall → Type
  | .hasWork _ | .dispatch _ => Bool
  | .occupancy _ => Nat
  | .iteration _ => IterResult
  | _ => Unit

def original : (call : BatchCall) → M call.Result
  | .napi => Env.napiSoftirq
  | .irqExit => Env.napiIrqExit
  | .hasWork a => Env.Activation.hasWork a
  | .occupancy a => Env.Activation.occupancy a
  | .cryptAhead pid => Env.cryptAhead pid
  | .iteration a => Env.Activation.iter a
  | .activation a => Env.Activation.run a
  | .dispatch worker => Env.dispatch worker
  | .schedule stack => Env.schedule stack
  | .nestedResched worker => Env.nestedResched worker

def observed : (call : BatchCall) → PrefixM LifetimeEvent call.Result
  | .napi => napiSoftirqPrefix
  | .irqExit => napiIrqExitPrefix
  | .hasWork a => activationHasWorkPrefix a
  | .occupancy a => activationOccupancyPrefix a
  | .cryptAhead pid => cryptAheadPrefix pid
  | .iteration a => activationIterPrefix a
  | .activation a => activationRunPrefix a
  | .dispatch worker => dispatchPrefix worker
  | .schedule stack => schedulePrefix stack
  | .nestedResched worker => nestedReschedPrefix worker

theorem erases (call : BatchCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | napi => exact napiSoftirqPrefix_erases
  | irqExit => exact napiIrqExitPrefix_erases
  | hasWork a => exact activationHasWorkPrefix_erases a
  | occupancy a => exact activationOccupancyPrefix_erases a
  | cryptAhead pid => exact cryptAheadPrefix_erases pid
  | iteration a => exact activationIterPrefix_erases a
  | activation a => exact activationRunPrefix_erases a
  | dispatch worker => exact dispatchPrefix_erases worker
  | schedule stack => exact schedulePrefix_erases stack
  | nestedResched worker => exact nestedReschedPrefix_erases worker

theorem allocation (call : BatchCall) : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe call.observed := by
  cases call with
  | napi => exact napiSoftirqPrefix_allocation
  | irqExit => exact napiIrqExitPrefix_allocation
  | hasWork a => exact activationHasWorkPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) (ProductTxContracts.ofNative allocationTx) a
  | occupancy a => exact activationOccupancyPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) a
  | cryptAhead pid => exact cryptAheadPrefix_allocation pid
  | iteration a => exact activationIterPrefix_allocation a
  | activation a => exact activationRunPrefix_allocation a
  | dispatch worker => exact dispatchPrefix_allocation worker
  | schedule stack => exact schedulePrefix_allocation stack
  | nestedResched worker => exact nestedReschedPrefix_allocation worker

end BatchCall
end Leanux.Proofs.WG.Lifetimes
