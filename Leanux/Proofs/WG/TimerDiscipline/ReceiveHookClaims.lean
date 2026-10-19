import Leanux.Proofs.WG.TimerDiscipline.ReceiveHookBridge
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.ReceiveHookJournal
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Queues
open HookJournal
theorem Inspection.Valid.facts (pid : PeerId) (pkt : RxPacket) (ep : Endpoint)
    (before : Campaign2.Snapshot) (result : Inspection)
    (valid : result.Valid pid pkt ep before) : result.Facts pid := by
  obtain ⟨g,ambient,_,rfl⟩ := valid
  exact observation_facts pid pkt ep g ambient

/-- Source-linked receipts from the actual complete caller, including a failing
hook and all earlier hooks before a later Stop. This local theorem does not
infer upstream AEAD authenticity from arbitrary consume arguments. -/
theorem original_consume_hooks (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Campaign2.Observes (consumeDataDone pid pkt ep) (fun _=>True)
      (fun before outcome=>∃ result : Inspection,
        result.outcome = outcome ∧ result.Valid pid pkt ep before ∧ result.Facts pid) := by
  intro g ambient _
  exact ⟨observation pid pkt ep g ambient,observation_erases pid pkt ep g ambient,
    observation_valid pid pkt ep g ambient,observation_facts pid pkt ep g ambient⟩

end Leanux.Proofs.WG.TimerDiscipline.ReceiveHookJournal
