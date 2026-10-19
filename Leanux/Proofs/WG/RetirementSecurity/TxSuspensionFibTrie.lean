import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionFibResize

/-! Native trie insertion, removal and lookup frames for actual suspended
workers. Branch operands and aliases remain those of the original execution. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Fib
open Leanux Leanux.Net Leanux.Net.Fib
open Leanux.Proofs.Framing Lifetimes Queues

theorem rebalance (p : Path) : Keeps (trieRebalance p) := by
  suspension_source [trieRebalance] using [node,compare,resize_node,node_set,invariant]

theorem push_suffix (p : Path) (slen : Nat) : Keeps (nodePushSuffix p slen) := by
  suspension_source [nodePushSuffix] using [node,compare,node_set]

theorem pull_suffix (p : Path) (slen : Nat) : Keeps (nodePullSuffix p slen) := by
  suspension_source [nodePullSuffix] using [node,branch,compare,update_suffix,node_set]

theorem find_node (key : Nat) : Keeps (findNode key) := by
  suspension_source [findNode] using [get_trie,branch,compare,invariant]

theorem find_alias (aliases : Option (List FibAlias)) (slen dscp prio tbId : Nat) (first : Bool) : Keeps (findAlias aliases slen dscp prio tbId first) := by
  suspension_source [findAlias] using [branch,compare,invariant,table]

theorem insert_node (tp : Path) (fa : FibAlias) (key : Nat) : Keeps (insertNode tp fa key) := by
  suspension_source [insertNode] using [leaf_new,branch,invariant,node,tnode_new,put_child,put_root,node_set,push_suffix,rebalance,set_trie,get_trie]

theorem insert_alias (tp : Path) (l : Option Path) (fa : FibAlias) (before : Option Nat) (key : Nat) : Keeps (insertAlias tp l fa before key) := by
  suspension_source [insertAlias] using [branch,insert_node,invariant,node,node_set,push_suffix]

theorem remove_alias (tp l : Path) (index : Nat) : Keeps (removeAlias tp l index) := by
  suspension_source [removeAlias] using [node,node_set,branch,compare,invariant,pull_suffix,put_root,rebalance,set_trie,get_trie]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Fib
