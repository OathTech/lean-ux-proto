import Leanux.Proofs.WG.Noise.DriverTagAdapterSource
import Leanux.Proofs.WG.Noise.ReceptionCoverageSource
import Leanux.Proofs.WG.Noise.ReceiveStepCoverageSource
import Leanux.Proofs.WG.Noise.ReceiveStepCallerClaims
import Leanux.Proofs.WG.Noise.InitiationCoverageSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Origins

/-- The legacy receive observer's unrecorded gate/cookie leaves retain tags. -/
theorem reception_legacy_coverage (entry : TagMap) (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h g _ => ReceptionCaller.NativeCoverage entry h g) (fun _ => True)
      (ReceptionCaller.observe msg src) := by
  have cookie : StatePrefixPreserves (fun h g _ => ReceptionCaller.NativeCoverage entry h g) (fun _ => True)
      (liftWGPrefix (cookieMessageConsume msg)) :=
    ReceptionCaller.lift_coverage_exact entry _ (fun g ambient result final after run =>
      ReceptionTagSupport.cookieMessageConsume_tag_frame msg g.dev g ambient result final after rfl run)
  have load : StatePrefixPreserves (fun h g _ => ReceptionCaller.NativeCoverage entry h g) (fun _ => True)
      (liftWGPrefix Cookies.loadPhase) :=
    ReceptionCaller.lift_coverage_exact entry _ (fun g ambient result final after run =>
      ReceptionCaller.loadPhase_tag_frame g.dev g ambient result final after rfl run)
  have mac (loaded : Bool) : StatePrefixPreserves (fun h g _ => ReceptionCaller.NativeCoverage entry h g) (fun _ => True)
      (liftWGPrefix (cookieValidatePacket msg src loaded)) :=
    ReceptionCaller.lift_coverage_exact entry _ (fun g ambient result final after run =>
      cookieValidatePacket_spec_tagMap_variant msg src loaded g.dev g ambient result final after rfl run)
  unfold ReceptionCaller.observe HandshakeSources.receptionWith
  simp (config := {zeta := false}) only [← ReceptionCaller.observeAfter_eq]
  dsimp (config := {zeta := false}) only [ReceptionCaller.ops]
  change StatePrefixEnsures (fun h g _ => ReceptionCaller.NativeCoverage entry h g) (fun _ => True) _
    (fun _ h g _ => ReceptionCaller.NativeCoverage entry h g)
  repeat' first
    | (maintenance_head ReceptionCaller.observeAfter; exact ReceptionCaller.after_coverage entry _ _ _ _)
    | exact cookie
    | exact load
    | exact mac _
    | (maintenance_lift_action_head branch; exact ReceptionCaller.ambient_coverage entry (AmbientM.branch _ _))
    | (maintenance_head Pure.pure; exact ReceptionCaller.pure_coverage entry _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h g _ => ReceptionCaller.NativeCoverage entry h g))
    | maintenance_intro
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)

def reception (msg : List UInt8) (src : SkbSource) : Obs Unit :=
  appendHelpers (ReceptionCaller.observe msg src)

theorem reception_erases (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (reception msg src) (receiveHandshakePacket msg src) :=
  appendHelpers_erases _ _ (ReceptionCaller.observe_erases msg src)

theorem reception_preserves (entry : TagMap) (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (reception msg src) := by
  apply appendHelpers_preserves entry
  · intro g ambient
    exact (ReceptionCaller.observe_valid msg src g ambient [] (by intro r member; cases member)).choose_spec.2.1
  · intro g ambient result final after receipts run
    have normal := (reception_legacy_coverage (responseTagMap g.dev) msg src g ambient []
      (TagsRetained.refl _)).choose_spec.2.2
    simp only [runWGPrefix,runStatePrefix] at run
    simpa only [run,ReceptionCaller.NativeCoverage] using normal

theorem initiation_receipt_valid (pid : PeerId) (receipt : TagReceipt)
    (valid : InitiationCaller.ReceiptValid pid receipt) : ReceptionCaller.ReceiptValid receipt := by
  obtain ⟨g,ambient,message,final,after,run,rfl⟩ := valid
  refine ⟨g,ambient,final,after,rfl,rfl,?_⟩
  change ((createInitiation pid).run g).run ambient >>= (fun ((x,next),inputs) =>
    Except.ok ((TagReturn.created x,next),inputs)) = _
  rw [run]
  rfl

theorem initiation_call_valid (pid : PeerId) (entry : Campaign2.Snapshot)
    (call : InitiationCaller.Call) (facts : InitiationCaller.CallFacts pid entry call) :
    ReceptionCaller.ValidHistory call.receipts := by
  cases call with
  | rateLimited => intro r member; cases member
  | noCreation receipt =>
    intro r member
    have same : r = receipt := by simpa [InitiationCaller.Call.receipts] using member
    subst r
    exact initiation_receipt_valid pid receipt facts.2.2.2.1
  | created message receipt =>
    intro r member
    have same : r = receipt := by simpa [InitiationCaller.Call.receipts] using member
    subst r
    exact initiation_receipt_valid pid receipt facts.2.2.2.1

def initiation (pid : PeerId) : Obs Unit :=
  completedHelpers (InitiationCaller.observe pid) (fun _ => ()) InitiationCaller.Call.receipts

def initiationWorker (pid : PeerId) : Obs Unit :=
  completedHelpers (InitiationCaller.observeWorker pid) (fun _ => ()) InitiationCaller.Call.receipts

theorem initiation_erases (pid : PeerId) :
    ErasesStatePrefix (initiation pid) (sendHandshakeInitiation pid) := by
  rw [← InitiationCaller.observe_erases pid]
  exact completedHelpers_erases _ _ _

theorem initiationWorker_erases (pid : PeerId) :
    ErasesStatePrefix (initiationWorker pid) (handshakeSendWorker pid) := by
  rw [← InitiationCaller.observeWorker_erases pid]
  exact completedHelpers_erases _ _ _

theorem initiation_preserves (entry : TagMap) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (initiation pid) := by
  apply completedHelpers_preserves entry
  · intro g ambient result final after run
    exact initiation_call_valid pid (Campaign2.snapshot g ambient) result
      (InitiationCaller.observe_facts pid (Campaign2.snapshot g ambient)
        g ambient result final after rfl run)
  · intro g ambient result final after run
    exact InitiationCaller.observe_coverage pid (Campaign2.snapshot g ambient)
      g ambient result final after rfl run

theorem initiationWorker_preserves (entry : TagMap) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (initiationWorker pid) := by
  apply completedHelpers_preserves entry
  · intro g ambient result final after run
    exact initiation_call_valid pid (Campaign2.snapshot g ambient) result
      (InitiationCaller.observeWorker_facts pid (Campaign2.snapshot g ambient)
        g ambient result final after rfl run)
  · intro g ambient result final after run
    exact InitiationCaller.observeWorker_coverage pid (Campaign2.snapshot g ambient)
      g ambient result final after rfl run

def receiveStepCompleted : Obs Bool :=
  completedHelpers ReceiveStepCaller.observeStep (fun r => r.poll.value) (fun r => r.poll.receipts)

theorem receiveStepCompleted_erases : ErasesStatePrefix receiveStepCompleted receiveStep := by
  rw [← ReceiveStepCaller.observeStep_discard]
  exact completedHelpers_erases _ _ _

theorem receiveStepCompleted_preserves (entry : TagMap) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory receiveStepCompleted := by
  apply completedHelpers_preserves entry
  · intro g ambient result final after run
    have shape := (ReceiveStepCaller.original_receiveStep_receipt (Campaign2.snapshot g ambient)
      g ambient result final after rfl run).2
    obtain ⟨d,device,shape⟩ := shape
    cases poll : result.poll with
    | empty => intro r member; simp [ReceiveStepCaller.PollResult.receipts] at member
    | consumed msg src call =>
      simp only [poll] at shape
      intro r member
      exact (shape.2.2.2.2.2 r member).1
  · exact ReceiveStepCaller.observeStep_coverage

end Leanux.Proofs.WG.Noise.DriverTags
