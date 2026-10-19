import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalPairSource

/-! Projected original-call outcome agreement and actual receipt grammar for response sending, packet reception, and receiveStep. The claims are unconditional on completion; global initialized-history uniqueness is separate. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Origins

theorem original_response (pid : PeerId) :
    (do let result←inspect (response pid);pure result.1)=Campaign2.inspect (sendHandshakeResponse pid) ∧
    Campaign2.Returns (inspect (response pid)) (fun _=>True)
      (fun result _=>ValidHistory result.2 ∧ Paired result.2 ∧
        ∀serial,result.2.countP (fun e=>e.sessionId==some serial)=
          result.2.countP (fun e=>e.derivedId==some serial)) :=
  ⟨inspect_source _ _ (response_erases pid),inspect_facts _ (response_valid pid) (response_paired pid)⟩
theorem original_reception (msg : List UInt8) (src : SkbSource) :
    (do let result←inspect (reception msg src);pure result.1)=Campaign2.inspect (receiveHandshakePacket msg src) ∧
    Campaign2.Returns (inspect (reception msg src)) (fun _=>True)
      (fun result _=>ValidHistory result.2 ∧ Paired result.2 ∧
        ∀serial,result.2.countP (fun e=>e.sessionId==some serial)=
          result.2.countP (fun e=>e.derivedId==some serial)) :=
  ⟨inspect_source _ _ (reception_erases msg src),inspect_facts _ (reception_valid msg src) (reception_paired msg src)⟩
theorem original_step :
    (do let result←inspect step;pure result.1)=Campaign2.inspect receiveStep ∧
    Campaign2.Returns (inspect step) (fun _=>True)
      (fun result _=>ValidHistory result.2 ∧ Paired result.2 ∧
        ∀serial,result.2.countP (fun e=>e.sessionId==some serial)=
          result.2.countP (fun e=>e.derivedId==some serial)) :=
  ⟨inspect_source _ _ step_erases,inspect_facts _ step_valid step_paired⟩

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
