import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalProjection
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1Placement

/-! The initialized exchange result and the final causal observer describe one
source execution. The exact ordered projection also retains native receipts
before a later Stop; no completed final runner state is required. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausal
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects CausalJournal

theorem history_project (trace : Runner.Trace) (placeholders : Bool) :
    (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      (runPrefixOuter (execute trace placeholders) []).2.filterMap exchange? :=
  congrArg Prod.snd (execute_projects trace placeholders [])

theorem initialized (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool) :
    Exchange.History ((runPrefixOuter (execute trace placeholders) []).2.filterMap exchange?)
      (Exchange.replay ((runPrefixOuter (execute trace placeholders) []).2.filterMap exchange?)) := by
  have history := Exchange.initialized facts config traffic trace placeholders
  rwa [history_project] at history

theorem session_position (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.exchange (.session pid r) :: post) :
    (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre.filterMap exchange? ++ Exchange.Event.session pid r :: post.filterMap exchange? := by
  rw [history_project,position,List.filterMap_append,List.filterMap_cons]
  rfl

/-- The exact session receipt in the final journal supplies both its actual
created-key cut and its cleared handshake. Final slot residency is discharged
separately by the local H1 placement contract at the same actual entry. -/
theorem session_created_and_cleared (facts : H1DriverSourceFacts)
    (config : H1ConfigurationTagFrames) (traffic : H1TrafficTagFrames)
    (trace : Runner.Trace) (placeholders : Bool) (pre post : List Event)
    (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.exchange (.session pid r) :: post) (success : r.value = true) :
    Exchange.SessionMaterialCut pid r ∧ handshakeTagAt r.after pid = some HANDSHAKE_ZEROED ∧
    (∀ other, other ≠ pid → handshakeTagAt r.after other = handshakeTagAt r.before other) ∧
    r.after.keypairCounter = r.before.keypairCounter + 1 :=
  ⟨Exchange.initialized_session_material facts config traffic trace placeholders _ _ pid r
    (session_position trace placeholders pre post pid r position) success,
   Exchange.initialized_session_clears facts config traffic trace placeholders _ _ pid r
    (session_position trace placeholders pre post pid r position) success⟩

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausal
