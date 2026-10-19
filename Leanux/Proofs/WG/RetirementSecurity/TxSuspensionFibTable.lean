import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionFibTrie

/-! Actual table allocation, sharing, insertion and deletion preserve the
suspended-activation list used by the TX service carrier. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Fib
open Leanux Leanux.Net Leanux.Net.Fib
open Leanux.Proofs.Framing Lifetimes Queues

theorem cache_flush  : Keeps (rtCacheFlush) := by
  unfold rtCacheFlush
  suspension_source [] using [table_modify]

theorem addr_gen  : Keeps (devAddrGenidBump) := by
  unfold devAddrGenidBump
  suspension_source [] using [table_modify]

theorem device_up (dev : Nat) : Keeps (deviceUp dev) := by
  unfold deviceUp
  suspension_source [] using []

theorem device_inet (dev : Nat) : Keeps (deviceHasInet dev) := by
  unfold deviceHasInet
  suspension_source [] using []

theorem device_addrs (dev : Nat) : Keeps (deviceAddrs dev) := by
  unfold deviceAddrs
  suspension_source [] using []

theorem device_plen (dev addr : Nat) : Keeps (devicePlen dev addr) := by
  unfold devicePlen
  suspension_source [] using []

theorem find_info (fi : FibInfo) : Keeps (findInfo fi) := by
  unfold findInfo
  simp (config := {zeta := false}) only [Std.TreeMap.forIn_eq_forIn_toList]
  suspension_source [] using [table]

theorem release_info (slot : FibInfoId) : Keeps (releaseInfo slot) := by
  unfold releaseInfo
  suspension_source [] using [table,invariant,table_modify]

theorem modify_info (slot : FibInfoId) (f : FibInfo→FibInfo) : Keeps (modifyInfo slot f) := by
  unfold modifyInfo
  suspension_source [] using [table,invariant,table_modify]

theorem valid_prefsrc (cfg : Config) (src : Nat) : Keeps (validPrefsrc cfg src) := by
  unfold validPrefsrc
  suspension_source [] using [inet_type]

theorem create_info (cfg : Config) : Keeps (createInfo cfg) := by
  unfold createInfo
  suspension_source [] using [env_result,device_inet,device_up,valid_prefsrc,select_address,table,find_info,modify_info,table_modify]

theorem modify_default (tb : Nat) (f : Nat→Nat) : Keeps (modifyNumDefault tb f) := by
  unfold modifyNumDefault
  suspension_source [] using [table_modify]

theorem table_insert (cfg : Config) : Keeps (tableInsert cfg) := by
  unfold tableInsert
  suspension_source [] using [create_info,branch,compare,invariant,table,find_node,find_alias,release_info,env_result,node,node_set,cache_flush,insert_alias,modify_default]

theorem notify_delete (aliases : List FibAlias) (index : Nat) : Keeps (notifyAliasDelete aliases index) := by
  unfold notifyAliasDelete
  suspension_source [] using [invariant,find_alias,branch,compare]

theorem table_delete (cfg : Config) : Keeps (tableDelete cfg) := by
  unfold tableDelete
  suspension_source [] using [find_node,find_alias,branch,compare,invariant,table,notify_delete,modify_default,remove_alias,cache_flush,release_info]

theorem table_flush (tb : Nat) (all : Bool) : Keeps (tableFlush tb all) := by
  unfold tableFlush
  suspension_source [] using [node,branch,compare,invariant,node_set,update_suffix,resize_node,set_trie,get_trie,table,notify_delete,release_info,put_root]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Fib
