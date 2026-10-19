import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingCompositionRoot
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingQueueRepaymentFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingQueueNativeFrames

/-! Exact queued-initiation decision/install/append cuts retain the same
restored ledger. Repayment uses the actual decision's borrow and the fixed
peer-release source family. Decision and installation expose the native
getter and metadata-write cuts, with their original remainder. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier
set_option maxHeartbeats 600000

def queueEvent (pid : PeerId) (h : List Event) (w : WGWorld) (a : Ambient) : Event :=
  .queued ⟨CausalScope.current scope? h,pid,⟨(),w,Queued.queuedWorld pid w,a,a⟩⟩

def queuePending (pid : PeerId) (h : List Event) (w : WGWorld) (a : Ambient) : WGPrefix Event Unit :=
  emitStatePrefix (queueEvent pid h w a)

theorem queue_append_run (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (effects.append pid) w a h=(.ok (((),Queued.queuedWorld pid w),a),h++[queueEvent pid h w a]) :=
  TimerEffects.queue_completed Event.queued (CausalScope.current scope? h) pid w (Queued.queuedWorld pid w) a a h rfl

inductive QueuePoint (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    WGWorld → Ambient → List Event → WGPrefix Event Unit → Type 1 where
  | entry : QueuePoint pid w a h w a h (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false)
  | deciding (point : QueueNative.Point (QueueNative.decisionShape pid) w a v b rest) :
      QueuePoint pid w a h v b h (liftWGPrefix rest >>= Queued.suffix pid)
  | decision (native : ((Queued.decisionPrefix pid).run w).run a=.ok ((choice,v),b)) :
      QueuePoint pid w a h v b h (Queued.suffix pid choice)
  | repayment (decision : ((Queued.decisionPrefix pid).run w).run a=.ok ((some true,u),c))
      (point : PeerRetirement.Points.Point (some pid) u c h v b middle) :
      QueuePoint pid w a h v b middle point.remainder
  | installing (decision : ((Queued.decisionPrefix pid).run w).run a=.ok ((some false,u),c))
      (point : QueueNative.Point (QueueNative.installShape pid) u c v b rest) :
      QueuePoint pid w a h v b h (liftWGPrefix rest >>= fun _=>effects.append pid)
  | installed (decision : ((Queued.decisionPrefix pid).run w).run a=.ok ((some false,u),c))
      (native : ((Queued.install pid).run u).run c=.ok (((),v),b)) :
      QueuePoint pid w a h v b h (effects.append pid)
  | pending (decision : ((Queued.decisionPrefix pid).run w).run a=.ok ((some false,u),c))
      (installed : ((Queued.install pid).run u).run c=.ok (((),v),b)) :
      QueuePoint pid w a h (Queued.queuedWorld pid v) b h (queuePending pid h v b)
  | recorded (decision : ((Queued.decisionPrefix pid).run w).run a=.ok ((some false,u),c))
      (installed : ((Queued.install pid).run u).run c=.ok (((),v),b)) :
      QueuePoint pid w a h (Queued.queuedWorld pid v) b (h++[queueEvent pid h v b]) (pure ())

theorem QueuePoint.residual (point : QueuePoint pid w a h v b middle rest) :
    runWGPrefix (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false) w a h=runWGPrefix rest v b middle := by
  cases point with
  | entry=>rfl
  | deciding point=>
    rw [Queued.factor,Staging.Points.run_bind,runWGPrefix_lift,point.residual,
      Staging.Points.run_bind,runWGPrefix_lift]
  | decision native=>rw [Queued.run,native]
  | repayment decision point=>
    rw [Queued.run,decision]
    exact point.continuation
  | installing decision point=>
    rw [Queued.run,decision]
    simp only [Queued.suffix,Staging.Points.run_bind,runWGPrefix_lift,point.residual]
  | installed decision native=>
    rw [Queued.run,decision]
    simp only [Queued.suffix,Staging.Points.run_bind,runWGPrefix_lift,native]
  | pending decision installed=>
    rw [Queued.run,decision]
    simp only [Queued.suffix,Staging.Points.run_bind,runWGPrefix_lift,installed,queue_append_run]
    rfl
  | recorded decision installed=>
    rw [Queued.run,decision]
    simp only [Queued.suffix,Staging.Points.run_bind,runWGPrefix_lift,installed,queue_append_run]
    rfl

theorem QueuePoint.accounted (point : QueuePoint pid w a h v b middle rest)
    (before : Accounted h ledger debts locals w) : Accounted middle ledger debts locals v := by
  cases point with
  | entry=>exact before
  | deciding point=>exact point.accounted before
  | decision native=>exact ⟨Queued.decision_entry before.entry _ _ _ native,before.complete⟩
  | repayment decision point=>
    exact funded_release_point
      ⟨Queued.decision_entry before.entry _ _ _ decision,before.complete⟩
      (Queued.decision_funded _ _ _ decision) point
  | installing decision point=>
    exact point.accounted ⟨Queued.decision_entry before.entry _ _ _ decision,before.complete⟩
  | installed decision native=>
    exact ⟨Queued.install_entry (Queued.decision_entry before.entry _ _ _ decision) _ _ _ native,before.complete⟩
  | pending decision installed=>
    exact (show Accounted h ledger debts locals _ from
      ⟨Queued.install_entry (Queued.decision_entry before.entry _ _ _ decision) _ _ _ installed,before.complete⟩).same_view
      (Queued.queued_view _ _)
  | recorded decision installed=>
    rename_i u c v
    have atWrite : Accounted h ledger debts locals (Queued.queuedWorld pid v) := (show Accounted h ledger debts locals _ from
      ⟨Queued.install_entry (Queued.decision_entry before.entry _ _ _ decision) _ _ _ installed,before.complete⟩).same_view
      (Queued.queued_view _ _)
    exact atWrite.append_quiet _ (by intro event member; cases List.mem_singleton.mp member; rfl)
      (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)

/-- The literal queued source retains the same account and continuation at
every fixed native point, including points before a later Stop. -/
theorem queue_every_point (before : Accounted h ledger debts locals w)
    (point : QueuePoint pid w a h v b middle rest) :
    Accounted middle ledger debts locals v ∧
      runWGPrefix (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false) w a h=
        runWGPrefix rest v b middle := ⟨point.accounted before,point.residual⟩

theorem queue_stopped_point (before : Accounted h ledger debts locals w)
    (point : QueuePoint pid w a h v b middle rest)
    (failed : runWGPrefix rest v b middle=(.error reason,last)) :
    Accounted middle ledger debts locals v ∧
      runWGPrefix (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false) w a h=
        (.error reason,last) := ⟨point.accounted before,point.residual.trans failed⟩

theorem queue_stopped (before : Accounted h ledger debts locals w)
    (performed : runWGPrefix (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false) w a h=(.error reason,last)) :
    last=h ∧
      ((((Queued.decisionPrefix pid).run w).run a=.error reason ∧ Accounted h ledger debts locals w) ∨
        ∃ u c,((Queued.decisionPrefix pid).run w).run a=.ok ((some false,u),c) ∧
          ((Queued.install pid).run u).run c=.error reason ∧ Accounted h ledger debts locals u) := by
  obtain ⟨same,cut⟩:=Queued.stopped pid before.entry a performed
  refine ⟨same,?_⟩
  rcases cut with ⟨native,_⟩|⟨u,c,decision,failed,entry⟩
  · exact Or.inl ⟨native,before⟩
  · exact Or.inr ⟨u,c,decision,failed,entry,before.complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
