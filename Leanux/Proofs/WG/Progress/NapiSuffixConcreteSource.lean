import Leanux.Proofs.WG.Progress.NapiSuffixSource
import Leanux.Proofs.WG.Progress.StackSuffixSource
import Leanux.Proofs.WG.Progress.CryptIterationRecordSource

/-! Concrete original poll/NAPI suffix contracts, discharging Stack delivery.
They close the actual encrypt/decrypt activation strict-record decrease on
normal return. No normal return or global worker service is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues

theorem rxPoll_retains (records : List HiddenRecord) (pid : PeerId) (budget : Nat) :
    Preserves (fun w : World=>Tail records w.ambient.hidden)
      (rxPoll pid budget (fun pkts=>pkts.forM Env.deliverInner)) :=
  rxPoll_retains_of_stack records (deliverInner_retains records) pid budget

theorem softirq_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.napiSoftirq :=
  softirq_retains_of_stack records (deliverInner_retains records)

theorem inline_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.pollScheduledInline :=
  inline_retains_of_stack records (deliverInner_retains records)

theorem irqExit_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.napiIrqExit :=
  irqExit_retains_of_stack records (deliverInner_retains records)

theorem encryptStep_original_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden)
      (encryptStep Env.checksumHelp Env.napiSoftirq) :=
  encryptStep_retains records Env.napiSoftirq (softirq_retains records)

theorem decryptStep_original_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden)
      (decryptStep Env.napiSoftirq Env.napiIrqExit) :=
  decryptStep_retains records Env.napiSoftirq Env.napiIrqExit
    (softirq_retains records) (irqExit_retains records)

theorem encryptActivation_strict (a : Activation) (worker : a.worker=.encryptWorker)
    (records : List HiddenRecord) :
    Hoare (Activation.run a) (fun w=>w.ambient.hidden=some records)
      (fun _ w=>StrictTail records w.ambient.hidden) :=
  encrypt_activation_strict softirq_retains a worker records

theorem decryptActivation_strict (a : Activation) (worker : a.worker=.decryptWorker)
    (records : List HiddenRecord) :
    Hoare (Activation.run a) (fun w=>w.ambient.hidden=some records)
      (fun _ w=>StrictTail records w.ambient.hidden) :=
  decrypt_activation_strict softirq_retains irqExit_retains a worker records

end Leanux.Proofs.WG.Progress.RecordSuffix
