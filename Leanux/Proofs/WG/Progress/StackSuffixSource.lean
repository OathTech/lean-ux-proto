import Leanux.Proofs.WG.Index.StackAmbientRulesSource
import Leanux.Proofs.WG.Progress.TransmitSuffixSource
import Leanux.Proofs.WG.Progress.StackSuffixFrames
import Leanux.Proofs.WG.Progress.StackIPv6SuffixSource

/-! Concrete original inner delivery, through existing Stack factories and exact erasure. No callback preservation premise remains. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Index
theorem deliverInner_retains (records : List HiddenRecord) (bytes : List UInt8) :
    Preserves (fun w:World=>Tail records w.ambient.hidden) (Env.deliverInner bytes) := by
  have source := StackAmbientRules.stack_rule (fun w:World=>Tail records w.ambient.hidden) bytes
    (fun family addr packets mtu=>native_product records _ (wgXmit_retains records family addr packets mtu))
    (fun sites=>liftAmbient_contract _ _ _ (skipCut_retains sites records))
    (fun src dst=>native_product records _ (native_liftRouting records _ (net_routeOutput4 records src dst)))
    (native_product records _ (native_getDev records))
    (fun dev=>native_product records _ (native_liftRouting records _ (net_neighbourClassify records dev)))
    (fun src dst=>native_product records _ (native_liftRouting records _ (net_routeInput4 records src dst)))
    (stack_getWG_retains records) (stack_modifyEnv_retains records)
    (stackReceive6_retains records)
  apply (hoare_iff_run _ _ _).mpr
  intro w value after pre run
  obtain ⟨suffix,append,safe,post⟩:=source w [] pre
  have original := (PendingStack.stackSource_erases bytes w []).trans run
  simpa only [original] using post

end Leanux.Proofs.WG.Progress.RecordSuffix
