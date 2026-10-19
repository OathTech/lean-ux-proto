import Leanux.Proofs.WG.Progress.LoopbackSuffixSource
import Leanux.Proofs.WG.Progress.StackIPv6SuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Normal-result suffix claims for two concrete stack-related operations. No full deliverInner, nonempty activation, termination or service claim is made. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing
theorem loopbackSend_record_suffix (records : List HiddenRecord)
    (sites : List HiddenSite) (raised : Bool) :
    Campaign2.Ensures (loopbackSend sites raised)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (loopbackSend_retains records sites raised g)
    a (value,after) b (pre ▸ tail_self records) run

theorem stackReceive6_record_suffix (records : List HiddenRecord) (pkt : List UInt8) :
    Campaign2.Product.Ensures (Env.Stack.receive6 pkt)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (stackReceive6_retains records pkt)
    w value after (pre ▸ tail_self records) run
end Leanux.Proofs.WG.Progress.RecordSuffix
