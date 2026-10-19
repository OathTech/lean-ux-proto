import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsHistory

/-! History predicates pass through nested native repayment paths only with
the actual release callback's contract. Native state preservation is separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged
open RetirementSecurity.NestedPeerRelease
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem nested_rxFinish_history {Safe : List E → Prop} (hooks : Hooks E)
    (release : ∀ peer, StateHistorySafe Safe (hooks.peerRelease peer))
    (pid : PeerId) (ready : Packets.RxReady) :
    StateHistorySafe Safe (rxFinishWith (nestedOps hooks) pid ready) := by
  unfold rxFinishWith rxAfterLookupWith
  dsimp only [nestedOps]
  repeat' first
    | (driver_history_head Hooks.peerRelease; exact release _)
    | driver_state_history_step

end Leanux.Proofs.WG.TransmitSecurity.Driver
