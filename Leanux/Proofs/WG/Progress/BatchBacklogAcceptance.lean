import Leanux.Proofs.WG.Progress.BatchBacklogModel

set_option synthInstance.maxSize 1024
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Runner

def accepted : Bool :=
  match executeTrace pendingTrace with
  | .ok _ => true
  | .error _ => false

/-- The historical accepted fixture is now rejected by the actual batch boundary. -/
theorem pendingTrace_accepted : accepted = false := by decide +kernel

def rejectionDetails : Option (Nat × String × String) :=
  match executeTrace pendingTrace with
  | .error (index, .outsideDomain site reason) => some (index, site, reason)
  | _ => none

theorem pendingTrace_rejectionDetails : rejectionDetails =
    some (1, "drivers/net/wireguard/queueing.h:128",
      "work the batch queued outlived the guest's wait (its records would be missing)") := by
  decide +kernel

theorem pendingTrace_rejected : executeTrace pendingTrace =
    .error (1, .outsideDomain "drivers/net/wireguard/queueing.h:128"
      "work the batch queued outlived the guest's wait (its records would be missing)") := by
  have detail := pendingTrace_rejectionDetails
  unfold rejectionDetails at detail
  cases run : executeTrace pendingTrace with
  | ok result => simp [run] at detail
  | error pair =>
    obtain ⟨index, stop⟩ := pair
    cases stop with
    | outsideDomain site reason =>
      simp [run] at detail
      obtain ⟨rfl, rfl, rfl⟩ := detail
      rfl
    | invariant reason => simp [run] at detail
    | hidden reason => simp [run] at detail

end Leanux.Proofs.WG.Progress
