import Leanux.Proofs.WG.Index.TransmitAmbientRulesSource
import Leanux.Proofs.WG.Progress.RoutingIPv4SuffixSource
import Leanux.Proofs.WG.Progress.LoopbackSuffixSource
import Leanux.Proofs.WG.Progress.AllowedLookupSuffixSource
import Leanux.Proofs.WG.Progress.RxPrimitiveSuffixSource

/-! Original WG transmit paths preserve a supplied-record suffix, including negative returns, ICMP loopback, staging and release. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Index
theorem lookupDst_retains (records : List HiddenRecord) (family addr : Nat) :
    NativeKeeps records (lookupDst family addr) := by
  env_operation_source [lookupDst]
    using [native_getDev, native_branch, lookup_retains, native_pure, native_bind]

theorem xmitTrim_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (xmitTrim pid) := by
  unfold xmitTrim
  simp (config := {zeta:=false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_modifyDev
    | env_operation_fact native_branch
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_forIn
    | env_operation_step

theorem xmitSplice_retains (records : List HiddenRecord) (pid : PeerId) (packets : List Packet) :
    NativeKeeps records (xmitSplice pid packets) := by
  env_operation_source [xmitSplice] using [native_getPeer,native_setPeer,native_bind]

theorem wgXmit_retains (records : List HiddenRecord) (family addr : Nat)
    (packets : List Packet) (mtu : Nat) :
    NativeKeeps records (wgXmit family addr packets mtu) := by
  apply Completion.of_rules
  apply TransmitAmbientRules.wgXmit_rule
  · intro site value; exact Completion.to_rules records _ (native_branch records site value)
  · exact Completion.to_rules records _ (lookupDst_retains records family addr)
  · intro pid; exact Completion.to_rules records _ (xmitTrim_retains records pid)
  · intro pid xs; exact Completion.to_rules records _ (xmitSplice_retains records pid xs)
  · intro pid; exact Completion.to_rules records _ (staged_retains records pid)
  · intro peer; exact Completion.to_rules records _ (peerPut_retains records peer)
  · intro sites raised; exact Completion.to_rules records _ (loopbackSend_retains records sites raised)
  · intro src dst; exact Completion.to_rules records _
      (native_liftRouting records _ (net_routeOutput4 records src dst))
  · intro dev addr; exact Completion.to_rules records _
      (native_liftRouting records _ (net_inetDevAddrType records dev addr))
  · intro dev; exact Completion.to_rules records _
      (native_liftRouting records _ (net_neighbourClassify records dev))
  · intro sites; exact Completion.to_rules records _ (native_skipCutSites records sites)
  · intro site; exact Completion.to_rules records _ (native_envOk records site)
  · exact Completion.to_rules records _ (native_modifyDev records _)

end Leanux.Proofs.WG.Progress.RecordSuffix
