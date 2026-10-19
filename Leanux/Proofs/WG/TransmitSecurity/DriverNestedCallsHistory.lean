import Leanux.Proofs.WG.TransmitSecurity.DriverNestedHistory
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseHistory

/-! Nested native callbacks transport the supplied history predicate through
their real peer repayments, including stopped outer calls. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
open RetirementSecurity.NestedPeerRelease
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem nested_history_ops {Safe : List E → Prop} (g : Hooks E)
    (release : ∀ peer, StateHistorySafe Safe (g.peerRelease peer)) :
    Ops.History Safe (nestedOps g) where
  step := History.state_lift
  release := release

theorem clearWorker_history {Safe : List E → Prop} (g : Hooks E)
    (release : ∀ peer, StateHistorySafe Safe (g.peerRelease peer)) :
    ProductHistorySafe Safe (clearWorkerObserved g) := by
  unfold clearWorkerObserved oneClearWith runWorkerPrefix
  repeat' first
    | (driver_history_head clearWith;
       exact (clear_history (nested_history_ops g release) _).liftWGObserver)
    | driver_product_history_step

theorem receiveEntry_history {Safe : List E → Prop} (g : Hooks E)
    (release : ∀ peer, StateHistorySafe Safe (g.peerRelease peer)) (msg : Key) (src : SkbSource) :
    ProductHistorySafe Safe (receiveEntryObserved g msg src) :=
  (receive_history (nested_history_ops g release) msg src).liftWGObserver

theorem dumpDispatch_history {Safe : List E → Prop} (g : Hooks E)
    (release : ∀ peer, StateHistorySafe Safe (g.peerRelease peer)) (call : Syscall) :
    ProductHistorySafe Safe (dumpDispatch (nestedOps g) call) := by
  unfold dumpDispatch
  cases call <;> simp only [dumpDispatchWith]
  all_goals repeat' first
    | (driver_history_head dumpDeviceWith;
       exact (dumpDevice_history (nested_history_ops g release) _).liftWGObserver)
    | (driver_history_head dumpStartWith;
       exact (dumpStart_history (nested_history_ops g release) _ _).liftWGObserver)
    | (driver_history_head dumpReceiveWith;
       exact (dumpReceive_history (nested_history_ops g release) _).liftWGObserver)
    | (driver_history_head netlinkRequestWith; unfold netlinkRequestWith)
    | (driver_history_head socketCallOnWith; unfold socketCallOnWith)
    | driver_product_history_step

end Leanux.Proofs.WG.TransmitSecurity.Driver
