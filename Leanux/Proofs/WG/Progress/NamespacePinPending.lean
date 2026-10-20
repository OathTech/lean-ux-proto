import Leanux.Proofs.WG.Progress.RunnerBoundaryAuditSource

/-! Regression for the resolved namespace-pin alias finding. The concrete
input is outside the fixture domain, and direct typed execution refuses before
premature teardown. These are fail-noisy interpreter checks, not kernel proofs. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.NamespacePinPending
open Leanux Leanux.Runner

/-- The foreign fixture's pin is duplicated before its fixed holder is closed.
The final ordinary close drops the remaining alias. Default fd limit is 32. -/
def trace : Trace :=
  {id := "campaign2-namespace-pin-alias", foreign := true,
   ops := #[.dup (.literal 9), .wgNetnsClose, .close (.ref 0)]}

/-- Historical concrete input, now rejected by both parser and harness validator. -/
def input : String :=
  "{\"version\":1,\"id\":\"campaign2-namespace-pin-alias\",\"net_fixture\":\"foreign-creator\",\"ops\":[{\"op\":\"dup\",\"fd\":{\"literal\":9}},{\"op\":\"wg_netns_close\"},{\"op\":\"close\",\"fd\":{\"ref\":0}}]}"

/-- Keep the historical alias trace as a checked refusal at each independent
boundary: parsing, direct typed execution, and the exact boundary observer. -/
def reproduce : IO Unit := do
  match Lean.Json.parse input >>= Runner.parseTrace with
  | .ok _ => throw (IO.userError "namespace-pin alias: reserved descriptor unexpectedly parses")
  | .error message =>
    unless message == "descriptor literal 9 is the fixture's (reserved 0..9)" do
      throw (IO.userError s!"namespace-pin alias: parser refusal changed: {message}")
  match Runner.executeTrace trace true, executeTraceWithBoundaries trace true with
  | .error (index, .invariant message), .error (observedIndex, .invariant observedMessage) =>
    unless index == 1 && observedIndex == index && observedMessage == message &&
        message == "wg_netns_close: the pin's close did not drop the creating namespace's last reference (cleanup_net was not queued)" do
      throw (IO.userError "namespace-pin alias: original or audit queued-cleanup refusal changed")
    IO.println "Namespace-pin regression passed: reserved descriptor refused; direct typed execution and audit stop before teardown at operation 1"
  | _, _ => throw (IO.userError "namespace-pin alias: original or audit did not refuse the retained pin")

#eval reproduce

end Leanux.Proofs.WG.Progress.NamespacePinPending
