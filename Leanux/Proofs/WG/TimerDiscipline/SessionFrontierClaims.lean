import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierSource

/-! Unconditional original outcome agreement and allocation-order facts for the three concrete handshake callers. These are compositional caller results, not an initialized whole-driver frontier theorem. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

theorem original_response_allocation (pid : PeerId) :
    (do let result←inspect (response pid);pure result.1)=Campaign2.inspect (sendHandshakeResponse pid) ∧
    Campaign2.Returns (inspect (response pid)) (fun _=>True) (fun result _=>AllocationFacts result) :=
  ⟨inspect_source _ _ (response_erases pid),inspect_allocation _ (response_frontier pid) (response_paired pid)⟩

theorem original_reception_allocation (msg : List UInt8) (src : SkbSource) :
    (do let result←inspect (reception msg src);pure result.1)=Campaign2.inspect (receiveHandshakePacket msg src) ∧
    Campaign2.Returns (inspect (reception msg src)) (fun _=>True) (fun result _=>AllocationFacts result) :=
  ⟨inspect_source _ _ (reception_erases msg src),inspect_allocation _ (reception_frontier msg src) (reception_paired msg src)⟩

theorem original_step_allocation :
    (do let result←inspect step;pure result.1)=Campaign2.inspect receiveStep ∧
    Campaign2.Returns (inspect step) (fun _=>True) (fun result _=>AllocationFacts result) :=
  ⟨inspect_source _ _ step_erases,inspect_allocation _ step_frontier step_paired⟩

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
