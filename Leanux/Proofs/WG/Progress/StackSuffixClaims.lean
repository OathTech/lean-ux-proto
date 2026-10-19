import Leanux.Proofs.WG.Progress.StackSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Normal-result supplied-record suffix effects for the complete original transmit and inner-delivery calls. These are not finite-evaluation or successful-service theorems. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing
theorem wgXmit_record_suffix (records : List HiddenRecord) (family addr : Nat)
    (packets : List Packet) (mtu : Nat) :
    Campaign2.Ensures (wgXmit family addr packets mtu)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (wgXmit_retains records family addr packets mtu g)
    a (value,after) b (pre ▸ tail_self records) run
theorem deliverInner_record_suffix (records : List HiddenRecord) (bytes : List UInt8) :
    Campaign2.Product.Ensures (Env.deliverInner bytes)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (deliverInner_retains records bytes)
    w value after (pre ▸ tail_self records) run
end Leanux.Proofs.WG.Progress.RecordSuffix
