import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionCuts

/-! The socket routing calls preserve the native suspended actor list.
The trie may change its own accessed bits; this is solely the scheduler frame. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Leanux.Net.Fib

theorem table : Keeps getTable := by
  suspension_source [getTable] using []

theorem table_modify (f : Table→Table) : Keeps (modifyTable f) := by
  suspension_source [modifyTable] using []

theorem node (path : Path) : Keeps (Net.Fib.nodeAt path) := by
  suspension_source [Net.Fib.nodeAt,getTrie,getTable] using [invariant]

theorem node_set (path : Path) (n : Option KeyVector) : Keeps (Net.Fib.setNode path n) := by
  suspension_source [Net.Fib.setNode,setTrie,getTrie,getTable,modifyTable] using []

theorem good_nhc (fi : FibInfo) (flow : Flow) : Keeps (lookupGoodNhc fi flow) := by
  suspension_source [lookupGoodNhc] using [branch, compare]

set_option maxHeartbeats 1000000 in
theorem table_lookup (flow : Flow) : Keeps (tableLookup flow) := by
  suspension_source [tableLookup,getTrie] using [table, node, node_set, good_nhc, invariant, branch, compare, exhausted]

theorem inet_lookup (addr : Nat) : Keeps (inetLookupIfaddr addr) := by
  suspension_source [inetLookupIfaddr] using []

theorem inet_type (dev : Option Nat) (addr : Nat) : Keeps (inetDevAddrType dev addr) := by
  suspension_source [inetDevAddrType] using [table_lookup, table, invariant]

theorem select_address (dev scope : Nat) : Keeps (inetSelectAddr dev scope) := by
  suspension_source [inetSelectAddr,deviceAddrs] using []

theorem prefsrc (info : FibInfoId) : Keeps (resultPrefsrc info) := by
  suspension_source [resultPrefsrc,modifyInfo] using [table, table_modify, select_address, invariant]

theorem defaults (tb : Nat) : Keeps (numDefault tb) := by
  suspension_source [numDefault] using [table]

theorem default_select (res : Result) : Keeps (Net.fibSelectDefault res) := by
  suspension_source [Net.fibSelectDefault] using [node, table, invariant]

theorem route_output (src dst : Nat) : Keeps (Net.routeOutput4 src dst) := by
  suspension_source [Net.routeOutput4] using [inet_lookup, table_lookup, table, defaults, default_select, prefsrc, invariant, unsupported]

theorem route (family src dst : Nat) : Keeps (Net.routeLookup family src dst) := by
  suspension_source [Net.routeLookup] using [route_output]

theorem neighbour (dev : Nat) : Keeps (Net.neighbourClassify dev) := by
  suspension_source [Net.neighbourClassify] using [inet_type]

theorem socket_namespace {action : Net.M α} (frame : Keeps action) : Keeps (inSocketNs action) := by
  unfold inSocketNs inCreatorNs
  repeat' first | exact frame | suspension_step

theorem routing_lift {action : Net.M α} (frame : Keeps action) : Keeps (liftRouting action) := by
  intro g
  exact (frame _).bind (fun _=>SameView.pure _ _)

theorem routing_call {action : Net.M α} (frame : Keeps action) : Keeps (monadLift action : WG.M α) :=
  routing_lift frame

theorem routing_get : Keeps (getRouting : WG.M Net.Routing) :=
  routing_lift (map _ get)

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
