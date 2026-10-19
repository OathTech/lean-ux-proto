import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSessionProjection
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1Placement
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverInitialized

/-! The exchange session receipt is also an exact responder source cut. Its
configured identity and fresh slot premises come from this same initialized
execution; the operational C2 placement consequence remains explicit. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSession
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects CausalJournal

theorem history_project (trace : Runner.Trace) (placeholders : Bool) :
    (runPrefixOuter (Responder.DriverCuts.execute trace placeholders) []).2 =
      (runPrefixOuter (execute trace placeholders) []).2.filterMap cut? :=
  congrArg Prod.snd (execute_projects trace placeholders [])

theorem session_position (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.exchange (.session pid r) :: post) :
    (runPrefixOuter (Responder.DriverCuts.execute trace placeholders) []).2 =
      pre.filterMap cut? ++ Responder.DriverCuts.Event.session pid r :: post.filterMap cut? := by
  rw [history_project,position,List.filterMap_append,List.filterMap_cons]
  rfl

/-- The actual new allocation remains resident in the session's role-selected
slot. Entry guards are derived at the exact initialized exchange receipt,
including receipts retained before a later Stop. Only named native H1 edge
and rotation contracts are premises. -/
theorem initialized_session_placed (edges : H1ResponderCurrentEdges)
    (rotation : H1SessionPlacement) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.exchange (.session pid r) :: post) (success : r.value = true) :
    Exchange.SessionPlaced pid r := by
  have checked := Responder.DriverCuts.initialized_cut edges trace placeholders
    (pre.filterMap cut?) (post.filterMap cut?) (.session pid r)
    (session_position trace placeholders pre post pid r position)
  exact Exchange.session_placed rotation pid r checked.2 success checked.1.1 checked.1.2.2

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSession
