import Leanux.Proofs.WG.Progress.RecordSuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge
/-! Projected normal-return suffix guarantees for original hidden reads, passive stripping, peeking and rescheduling. Recordless inputs, callback termination and global scheduler adequacy remain separate. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Env Leanux.Proofs.Framing

theorem hidden_record_suffix (site : HiddenSite) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (hidden site : Leanux.M (List UInt8))
      (fun s => s.ambient.hidden = some records)
      (fun _ s => StrictTail records s.ambient.hidden) := by
  intro before value after pre run
  exact (hoare_iff_run _ _ _).mp (hidden_product_suffix site records)
    before value after pre run

theorem skip_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures (skipAmbient : Leanux.M Unit)
      (fun s => s.ambient.hidden = some records)
      (fun _ s => Tail records s.ambient.hidden) := by
  intro before value after pre run
  exact (hoare_iff_run _ _ _).mp (skip_product_suffix records)
    before value after pre run

theorem peek_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures (peekHiddenSite : Leanux.M (Option Nat))
      (fun s => s.ambient.hidden = some records)
      (fun _ s => Tail records s.ambient.hidden) := by
  intro before value after pre run
  exact (hoare_iff_run _ _ _).mp (peek_product_suffix records)
    before value after pre run

theorem condResched_record_suffix (worker : Worker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (condResched worker)
      (fun s => s.ambient.hidden = some records)
      (fun yielded s => Tail records s.ambient.hidden ∧
        (yielded = true → StrictTail records s.ambient.hidden)) := by
  intro before value after pre run
  exact (hoare_iff_run _ _ _).mp (condResched_suffix worker records)
    before value after pre run
end Leanux.Proofs.WG.Progress.RecordSuffix
