import Leanux.Proofs.WG.TimerDiscipline.SessionWheelSource

/-! Original response/reception/receiveStep outcomes agree on success and Stop. Every recorded derived hook has its actual adjacent successful session and, on normal hook completion, exact wheel consequences. No global allocation or enqueue uniqueness is claimed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

theorem original_response_wheel (pid : PeerId) :
    (do let result←inspect (response pid);pure result.1)=Campaign2.inspect (sendHandshakeResponse pid) ∧
    Campaign2.Returns (inspect (response pid)) (fun _=>True)
      (fun result _=>WheelHistoryFacts result.2) :=
  ⟨(original_response pid).1,inspect_wheel _ (response_valid pid) (response_paired pid)⟩

theorem original_reception_wheel (msg : List UInt8) (src : SkbSource) :
    (do let result←inspect (reception msg src);pure result.1)=Campaign2.inspect (receiveHandshakePacket msg src) ∧
    Campaign2.Returns (inspect (reception msg src)) (fun _=>True)
      (fun result _=>WheelHistoryFacts result.2) :=
  ⟨(original_reception msg src).1,inspect_wheel _ (reception_valid msg src) (reception_paired msg src)⟩

theorem original_step_wheel :
    (do let result←inspect step;pure result.1)=Campaign2.inspect receiveStep ∧
    Campaign2.Returns (inspect step) (fun _=>True) (fun result _=>WheelHistoryFacts result.2) :=
  ⟨original_step.1,inspect_wheel _ step_valid step_paired⟩

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
