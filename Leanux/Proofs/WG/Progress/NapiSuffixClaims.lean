import Leanux.Proofs.WG.Progress.NapiSuffixConcreteSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal-result suffixes and strict crypt-activation record decrease.
No successful evaluation or final state on a stopped call is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem rxPoll_record_suffix (records : List HiddenRecord) (pid : PeerId) (budget : Nat) :
    Campaign2.Product.Ensures (rxPoll pid budget (fun pkts=>pkts.forM Env.deliverInner))
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (rxPoll_retains records pid budget)
    w value after (pre ▸ tail_self records) run

theorem softirq_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.napiSoftirq
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (softirq_retains records)
    w value after (pre ▸ tail_self records) run

theorem inline_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.pollScheduledInline
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (inline_retains records)
    w value after (pre ▸ tail_self records) run

theorem irqExit_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.napiIrqExit
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (irqExit_retains records)
    w value after (pre ▸ tail_self records) run

theorem encryptActivation_record_strict (a : Activation) (worker : a.worker=.encryptWorker)
    (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run a)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>StrictTail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (encryptActivation_strict a worker records)
    w value after pre run

theorem decryptActivation_record_strict (a : Activation) (worker : a.worker=.decryptWorker)
    (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run a)
      (fun s=>s.ambient.hidden=some records) (fun _ s=>StrictTail records s.ambient.hidden) := by
  intro w value after pre run
  change w.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (decryptActivation_strict a worker records)
    w value after pre run

end Leanux.Proofs.WG.Progress.RecordSuffix
