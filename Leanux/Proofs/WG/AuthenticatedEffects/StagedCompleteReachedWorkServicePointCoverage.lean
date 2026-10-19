import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointDrain
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointAccounts

/-! Exhaustive actual executions and coverage of canonical service roots.
Every remainder is built from the original source spine; no error post-world
is asserted. Distinct deeper sender/repayment contracts remain explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal RetirementSecurity

inductive Root where
  | queued (pid : PeerId) (retry : Bool)
  | clear (pid : PeerId)
  | flushedClear (pid : PeerId)
  | scheduledSend
  | scheduledClear
  | drain (upTo : Option PeerId)

def Root.action : Root → PrefixM Event Unit
  | .queued pid retry => liftWGObserver (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid retry)
  | .clear pid => liftWGObserver (NestedPeerRelease.clearWith (Driver.nestedOps hooks) pid)
  | .flushedClear pid => liftWGObserver (NestedPeerRelease.flushedClearWith (Driver.nestedOps hooks) pid)
  | .scheduledSend => Driver.sendWorkerObserved hooks
  | .scheduledClear => Driver.clearWorkerObserved hooks
  | .drain upTo => liftWGObserver (Driver.sendDrainObserved hooks upTo)

noncomputable def Root.shape (root : Root) : Shape root.action := match root with
  | .queued pid retry => queuedShape pid retry
  | .clear pid => clearShape pid
  | .flushedClear pid => flushedClearShape pid
  | .scheduledSend => scheduledSendShape
  | .scheduledClear => scheduledClearShape
  | .drain upTo => drainShape upTo

theorem root_cases (root : Root) (performed : runPrefix root.action w h = (result,last)) :
    Execution root.shape w h result last := execution_cases _ performed

abbrev RootPoint (inside : ChildPoints) (root : Root) (w : World) (h : History) (u : World) (middle : History) :=
  ∃ site, Point inside root.shape w h site u middle

theorem source_covered {native inside : ChildPoints} {Good : History → World → Prop}
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (root : Root) (before : Carrier h w)
    (performed : runPrefix root.action w h = (result,last)) :
    Execution root.shape w h result last ∧
    ∀ site u middle, Point native root.shape w h site u middle →
      Point inside root.shape w h site u middle ∧ Good middle u ∧
      ∃ remainder, Residual children root.shape w h site u middle remainder ∧
        runPrefix remainder u middle = (result,last) := by
  refine ⟨root_cases root performed,?_⟩
  intro site u middle point
  have covered := point.coverage children
  obtain ⟨remainder,residual⟩ := point.residual children
  exact ⟨covered,covered.safe carrierGood children before,remainder,residual,residual.run.symm.trans performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
