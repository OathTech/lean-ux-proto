import Leanux.Proofs.WG.Progress.RunnerBoundaryAuditSource

/-! Accepted initialized placeholder execution with a retained namespace-pin
alias. This is a fail-noisy interpreter recipe, not a kernel-reduction proof. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.NamespacePinPending
open Leanux Leanux.Runner

/-- The foreign fixture's pin is duplicated before its fixed holder is closed.
The final ordinary close drops the remaining alias. Default fd limit is 32. -/
def trace : Trace :=
  {id := "campaign2-namespace-pin-alias", foreign := true,
   ops := #[.dup (.literal 9), .wgNetnsClose, .close (.ref 0)]}

/-- Matching concrete input, also accepted by the Python harness validator. -/
def input : String :=
  "{\"version\":1,\"id\":\"campaign2-namespace-pin-alias\",\"net_fixture\":\"foreign-creator\",\"ops\":[{\"op\":\"dup\",\"fd\":{\"literal\":9}},{\"op\":\"wg_netns_close\"},{\"op\":\"close\",\"fd\":{\"ref\":0}}]}"

/-- Check both the original result and its exact existing boundary observer. -/
def reproduce : IO Unit := do
  let .ok parsed := Lean.Json.parse input >>= Runner.parseTrace
    | throw (IO.userError "namespace-pin alias: concrete input no longer parses")
  let .ok parsedOutput := Runner.executeTrace parsed true
    | throw (IO.userError "namespace-pin alias: parsed original execution stopped")
  match Runner.executeTrace trace true, executeTraceWithBoundaries trace true with
  | .ok json, .ok audit =>
    unless json == audit.output && json == parsedOutput do
      throw (IO.userError "namespace-pin alias: original and audit outputs differ")
    let cuts := audit.boundaries.map fun (cut : RunnerBoundary) =>
      (cut.index, cut.result, cut.after.ambient.hidden.isSome, cut.after.ambient.pendingWork)
    unless cuts == [(0,10,false,[]),(1,0,false,[]),(2,0,false,[12])] do
      throw (IO.userError "namespace-pin alias: accepted pending boundary changed")
    IO.println "Namespace-pin alias reproduced: original accepts; final pending netnsCleanup is [12]"
  | _, _ => throw (IO.userError "namespace-pin alias: initialized trace unexpectedly stopped")

#eval reproduce

end Leanux.Proofs.WG.Progress.NamespacePinPending
