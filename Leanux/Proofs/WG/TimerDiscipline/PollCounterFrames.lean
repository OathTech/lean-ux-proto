import Leanux.Proofs.WG.TimerDiscipline.SessionCounterFrames
import Leanux.Proofs.WG.Noise.PendingPollFrames
import Leanux.Proofs.WG.Queues.RxNapiCuts

/-! Physical counter projections for the existing native poll and NAPI source factors. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.PollCounterFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open HandshakeJournal Lifetimes
theorem ambient {α : Type} (a : AmbientM α) : SameView (fun w : World=>w.wg.keypairCounter)
   (monadLift a : Leanux.M α) :=
   fun initial=>productAmbient_spec a (fun w=>w.wg.keypairCounter=initial) (fun _ _ hi=>hi)
theorem peer (pid : PeerId) : SameView (fun w : World=>w.wg.keypairCounter)
    (monadLift (getPeer pid) : Leanux.M Peer) :=
    counter_native_frame (counter_snapshot (Keypairs.WGFrames.getPeer_sameSnapshot pid))
theorem writePeer (pid : PeerId) (p : Peer) : SameView (fun w : World=>w.wg.keypairCounter)
    (monadLift (setPeer pid p) : Leanux.M Unit) :=
    counter_native_frame (counter_snapshot (Keypairs.WGFrames.setPeer_sameSnapshot pid p))
theorem packet (id : SkbId) : SameView (fun w : World=>w.wg.keypairCounter)
    (monadLift (getRxSkb id) : Leanux.M RxPacket) := by
    exact counter_native_frame (counter_snapshot (show Keypairs.SameSnapshot (getRxSkb id) from by snapshot_source [getRxSkb] using []))
theorem freePacket (id : SkbId) : SameView (fun w : World=>w.wg.keypairCounter)
    (monadLift (freeRxSkb id) : Leanux.M Unit) := by
    exact counter_native_frame (counter_snapshot (show Keypairs.SameSnapshot (freeRxSkb id) from by snapshot_source [freeRxSkb] using []))
theorem peek (q : PrevQueue SkbId) : SameView (fun w : World=>w.wg.keypairCounter)
    (monadLift q.peek : Leanux.M _) :=
    counter_native_frame (counter_snapshot (Keypairs.WGFrames.PrevQueue_peek_sameSnapshot q))
theorem endpoint (src : SkbSource) : SameView (fun w : World=>w.wg.keypairCounter)
    (monadLift (endpointFromSkb src) : Leanux.M _) :=
    counter_native_frame (counter_snapshot (Keypairs.WGTransitions.endpointFromSkb_sameSnapshot src))
theorem key (kid : Option KeypairId) (now : Bool) : SameView (fun w : World=>w.wg.keypairCounter)
    (monadLift (keypairPut kid now) : Leanux.M Unit) :=
    counter_native_frame (counter_retained (Noise.PendingTickets.keypairPut_retained kid now))
theorem release (pid : Option PeerId) : SameView (fun w : World=>w.wg.keypairCounter)
    (monadLift (peerPut pid) : Leanux.M Unit) :=
    counter_native_frame (counter_snapshot (Keypairs.WGFrames.peerPut_sameSnapshot pid))
theorem counter (kid nonce : Nat) : SameView (fun w : World=>w.wg.keypairCounter)
    (monadLift (counterValidate kid nonce) : Leanux.M Bool) :=
    counter_native_frame (counter_pending (Noise.PendingSession.counter_pending kid nonce))
theorem branch_counter (site : Decision) (value : Bool) :
    SameView (fun w : World=>w.wg.keypairCounter) (branch site value : Leanux.M Bool) := by
  unfold branch
  exact ambient _
theorem invariant_counter {α : Type} (reason : String) :
    SameView (fun w : World=>w.wg.keypairCounter) (invariant reason : Leanux.M α) := by
  env_operation_source [invariant] using [ambient]
theorem unsupported_counter {α : Type} (reason : String) :
    SameView (fun w : World=>w.wg.keypairCounter) (unsupported reason : Leanux.M α) := by
  env_operation_source [unsupported] using [ambient]
theorem ready (first : Option SkbId) : SameView (fun w : World=>w.wg.keypairCounter)
    (liftWG (WG.andM (branch .rxPollPacket first.isSome) do
      let some id := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((←getRxSkb id).state != .uncrypted))) := by
  apply counter_native_frame
  apply counter_snapshot
  snapshot_source [] using []
end Leanux.Proofs.WG.TimerDiscipline.PollCounterFrames

namespace Leanux.Proofs.WG.TimerDiscipline.PollCounterFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing HandshakeJournal Queues
theorem pending : CounterSame RxNapi.pendingSource := by
  apply counter_snapshot
  unfold RxNapi.pendingSource
  exact Keypairs.WGFrames.getDev_sameSnapshot.bind (fun _=>SameView.pure _ _)
theorem scheduled : CounterSame RxNapi.scheduledSource := by
  apply counter_snapshot
  unfold RxNapi.scheduledSource
  exact Keypairs.WGFrames.getDev_sameSnapshot.bind (fun _=>SameView.pure _ _)
end Leanux.Proofs.WG.TimerDiscipline.PollCounterFrames
