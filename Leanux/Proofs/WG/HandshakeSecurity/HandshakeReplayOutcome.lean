import Leanux.Proofs.WG.HandshakeSecurity.StaleInitiationContinuation
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSessionInitialized
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveInitialized

/-! The T4 conclusions at actual initialized execution occurrences. Final
journal positions are transported by exact ordered source projection. The
timestamp archive is its own exact source observer; no two histories are
identified merely because their final native results erase equally. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReplayOutcome
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects CausalJournal

abbrev journal (trace : Runner.Trace) (placeholders : Bool) :=
  (runPrefixOuter (execute trace placeholders) []).2

theorem response_once (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre between post : List Event) (first second : Key)
    (r s : WGRunWitness (Option PeerId)) (pid : PeerId)
    (position : journal trace placeholders = pre ++ Event.exchange (.consumeResponse first r) ::
      between ++ Event.exchange (.consumeResponse second s) :: post)
    (accepted₁ : r.value = some pid) (accepted₂ : s.value = some pid) :
    ∃ epoch₁ epoch₂, Exchange.ResponseAt (pre.filterMap exchange?) pid epoch₁ ∧
      Exchange.ResponseAt ((pre ++ Event.exchange (.consumeResponse first r) :: between).filterMap exchange?)
        pid epoch₂ ∧ epoch₁ < epoch₂ := by
  have projected : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre.filterMap exchange? ++ Exchange.Event.consumeResponse first r ::
      between.filterMap exchange? ++ Exchange.Event.consumeResponse second s :: post.filterMap exchange? := by
    unfold journal at position
    rw [ExchangeCausal.history_project,position,List.filterMap_append,List.filterMap_cons,
      List.filterMap_append,List.filterMap_cons]
    rfl
  simpa only [List.filterMap_append,List.filterMap_cons,exchange?,List.cons_append] using
    Exchange.initialized_response_once facts config traffic trace placeholders
      (pre.filterMap exchange?) (between.filterMap exchange?) (post.filterMap exchange?)
      first second r s pid projected accepted₁ accepted₂

theorem installed_once (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre between post : List Event) (r s : WGRunWitness Bool) (pid : PeerId)
    (position : journal trace placeholders = pre ++ Event.exchange (.session pid r) ::
      between ++ Event.exchange (.session pid s) :: post)
    (accepted₁ : r.value = true) (accepted₂ : s.value = true) :
    ∃ epoch₁ epoch₂, Exchange.InstallAt (pre.filterMap exchange?) pid epoch₁ ∧
      Exchange.InstallAt ((pre ++ Event.exchange (.session pid r) :: between).filterMap exchange?)
        pid epoch₂ ∧ epoch₁ < epoch₂ := by
  have projected : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre.filterMap exchange? ++ Exchange.Event.session pid r ::
      between.filterMap exchange? ++ Exchange.Event.session pid s :: post.filterMap exchange? := by
    unfold journal at position
    rw [ExchangeCausal.history_project,position,List.filterMap_append,List.filterMap_cons,
      List.filterMap_append,List.filterMap_cons]
    rfl
  simpa only [List.filterMap_append,List.filterMap_cons,exchange?,List.cons_append] using
    Exchange.initialized_install_once facts config traffic trace placeholders
      (pre.filterMap exchange?) (between.filterMap exchange?) (post.filterMap exchange?)
      r s pid projected accepted₁ accepted₂

def SingleAllocation (pid : PeerId) (r : WGRunWitness Bool) : Prop :=
  ∃ slot allocation device,
    (runWGPrefix (Installation.observed pid) r.before r.ambientBefore []).2 = [allocation] ∧
    allocation.Valid ∧ allocation.execution.value = some slot ∧
    allocation.execution.before.dev = some device ∧ slot = device.nextKeypairId ∧
    allocation.execution.after = keyAllocationWorld allocation.execution.before device allocation.word

/-- One successful session belongs to an actual earlier exchange, creates one
native allocation, installs that allocation in its role-selected slot, and
clears the handshake. These facts refer to the same final-journal receipt. -/
def Installed (pre : List Event) (pid : PeerId) (r : WGRunWitness Bool) : Prop :=
  SingleAllocation pid r ∧ Exchange.SessionPlaced pid r ∧ Exchange.SessionMaterialCut pid r ∧
  handshakeTagAt r.after pid = some HANDSHAKE_ZEROED ∧
  (∀ other, other ≠ pid → handshakeTagAt r.after other = handshakeTagAt r.before other) ∧
  r.after.keypairCounter = r.before.keypairCounter + 1 ∧
  ∃ epoch, Exchange.InstallAt (pre.filterMap exchange?) pid epoch ∧
    Exchange.Origin (pre.filterMap exchange?) pid epoch

theorem session (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (edges : H1ResponderCurrentEdges)
    (rotation : H1SessionPlacement) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : journal trace placeholders = pre ++ Event.exchange (.session pid r) :: post)
    (success : r.value = true) : Installed pre pid r := by
  have projected := ExchangeCausal.session_position trace placeholders pre post pid r position
  obtain ⟨material,cleared,others,count⟩ := ExchangeCausal.session_created_and_cleared
    facts config traffic trace placeholders pre post pid r position success
  exact ⟨Exchange.initialized_session_allocation facts config traffic trace placeholders _ _ pid r projected success,
    ExchangeCausalSession.initialized_session_placed edges rotation trace placeholders pre post pid r position success,
    material,cleared,others,count,
    (Exchange.initialized_install_count facts config traffic trace placeholders _ _ pid r projected success).2⟩

theorem refused_session (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : journal trace placeholders = pre ++ Event.exchange (.session pid r) :: post)
    (refused : r.value = false) : r.after = r.before :=
  Exchange.initialized_session_refusal_world facts config traffic trace placeholders _ _ pid r
    (ExchangeCausal.session_position trace placeholders pre post pid r position) refused

/-- The retained-peer freshness archive and the exact native exchange history
are initialized without a caller invariant. Their separate exact observers
cover committed writes and completed native exchange cuts before a later Stop. -/
theorem histories (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool) :
    TimestampArchive.History (runPrefixOuter (TimestampDriver.execute trace placeholders) []).2 ∧
    Exchange.History ((journal trace placeholders).filterMap exchange?)
      (Exchange.replay ((journal trace placeholders).filterMap exchange?)) :=
  ⟨TimestampArchive.initialized trace placeholders,
    ExchangeCausal.initialized facts config traffic trace placeholders⟩

end Leanux.Proofs.WG.HandshakeSecurity.ReplayOutcome
