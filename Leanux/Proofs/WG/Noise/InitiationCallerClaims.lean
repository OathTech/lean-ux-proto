import Leanux.Proofs.WG.Noise.InitiationCallerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.InitiationCaller
open Leanux Leanux.WG

theorem original_initiation_receipts (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observe pid) (fun s => s = entry)
      (fun call _ => RateObserved pid entry call ∧ CallFacts pid entry call) := by
  intro g ambient call final after pre run
  exact ⟨observe_rate pid entry g ambient call final after pre run,
    observe_facts pid entry g ambient call final after
      (congrArg Campaign2.Snapshot.tagAt pre) run⟩

theorem original_initiation_worker_receipts (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observeWorker pid) (fun s => s = entry)
      (fun call _ => RateObserved pid entry call ∧ CallFacts pid entry call) := by
  intro g ambient call final after pre run
  exact ⟨observeWorker_rate pid entry g ambient call final after pre run,
    observeWorker_facts pid entry g ambient call final after
      (congrArg Campaign2.Snapshot.tagAt pre) run⟩

theorem original_initiation_receipts_erases (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← observe pid; pure ()) (sendHandshakeInitiation pid) := by
  rw [observe_erases]
  intro g ambient pre
  rfl

theorem original_initiation_worker_receipts_erases (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← observeWorker pid; pure ()) (handshakeSendWorker pid) := by
  rw [observeWorker_erases]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Noise.InitiationCaller
