import Leanux.Proofs.WG.Progress.RoutingFibSuffixSource

/-! Concrete IPv4 route and address-classification suffix contracts. All callbacks are original functions with proved leaf contracts. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Proofs.Framing
theorem net_deviceAddrs (records : List HiddenRecord) (dev : Nat) :
    NetKeeps records (Net.Fib.deviceAddrs dev) := by
  env_operation_source [Net.Fib.deviceAddrs]
    using [net_get, net_pure, net_bind, net_ite]
theorem net_inetSelectAddr (records : List HiddenRecord) (dev scope : Nat) :
    NetKeeps records (Net.Fib.inetSelectAddr dev scope) := by
  env_operation_source [Net.Fib.inetSelectAddr]
    using [net_deviceAddrs, net_pure, net_bind, net_forIn, net_ite]
theorem net_modifyInfo (records : List HiddenRecord) (id : Net.Fib.FibInfoId)
    (f : Net.Fib.FibInfo→Net.Fib.FibInfo) :
    NetKeeps records (Net.Fib.modifyInfo id f) := by
  env_operation_source [Net.Fib.modifyInfo]
    using [net_getTable, net_modifyTable, net_invariant, net_pure, net_bind, net_ite]
theorem net_resultPrefsrc (records : List HiddenRecord) (info : Net.Fib.FibInfoId) :
    NetKeeps records (Net.Fib.resultPrefsrc info) := by
  env_operation_source [Net.Fib.resultPrefsrc]
    using [net_getTable, net_modifyInfo, net_inetSelectAddr, net_invariant,
      net_pure, net_bind, net_ite]
theorem net_numDefault (records : List HiddenRecord) (id : Nat) :
    NetKeeps records (Net.Fib.numDefault id) := by
  env_operation_source [Net.Fib.numDefault] using [net_getTable, net_pure, net_bind]
theorem net_fibSelectDefault (records : List HiddenRecord) (result : Net.Fib.Result) :
    NetKeeps records (Net.fibSelectDefault result) := by
  env_operation_source [Net.fibSelectDefault]
    using [net_nodeAt, net_getTable, net_invariant, net_pure, net_bind, net_forIn, net_ite]
theorem net_inetDevAddrType (records : List HiddenRecord) (dev : Option Nat) (addr : Nat) :
    NetKeeps records (Net.Fib.inetDevAddrType dev addr) := by
  env_operation_source [Net.Fib.inetDevAddrType]
    using [net_tableLookup, net_getTable, net_invariant, net_pure, net_bind, net_ite]
theorem net_routeOutput4 (records : List HiddenRecord) (src dst : Nat) :
    NetKeeps records (Net.routeOutput4 src dst) := by
  env_operation_source [Net.routeOutput4]
    using [net_inetLookupIfaddr, net_tableLookup, net_getTable, net_numDefault,
      net_fibSelectDefault, net_resultPrefsrc, net_invariant, net_unsupported,
      net_pure, net_bind, net_ite]
theorem net_routeLookup4 (records : List HiddenRecord) (src dst : Nat) :
    NetKeeps records (Net.routeLookup 4 src dst) := by
  simpa only [Net.routeLookup, BEq.rfl, ↓reduceIte] using net_routeOutput4 records src dst
theorem net_routeInput4 (records : List HiddenRecord) (src dst : Nat) :
    NetKeeps records (Net.routeInput4 src dst) := by
  env_operation_source [Net.routeInput4]
    using [net_tableLookup, net_inetLookupIfaddr, net_pure, net_bind, net_ite]
end Leanux.Proofs.WG.Progress.RecordSuffix
