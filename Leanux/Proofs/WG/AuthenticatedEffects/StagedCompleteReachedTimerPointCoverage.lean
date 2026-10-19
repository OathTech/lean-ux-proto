import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointChildren

/-! Canonical root coverage derives from the concrete source, with only
finite deeper native children and the explicit receipt-pending phase. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

inductive Root where
  | callback (pid : PeerId) (timer : PeerTimer)
  | selected (device : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
  | finished (token : Nat)

def Root.Result : Root → Type
  | .selected .. => Nat
  | _ => Unit

def Root.action (root : Root) : PrefixM Event root.Result := match root with
  | .callback pid timer => liftWGObserver (Driver.timerObserved hooks pid timer)
  | .selected device bound pid timer entry => hooks.timerSelected device bound pid timer entry
  | .finished token => hooks.timerFinished token

noncomputable def Root.shape (root : Root) : Shape root.action := match root with
  | .callback pid timer => callbackShape pid timer
  | .selected device bound pid timer entry => selectedShape device bound pid timer entry
  | .finished token => finishedShape token

theorem root_cases (root : Root) {result : Result root.Result} (performed : runPrefix root.action w h = (result,last)) :
    Execution root.shape w h result last := execution_cases _ performed

abbrev RootPoint (inside : ChildPoints) (root : Root) (w : World) (h : History) (u : World) (middle : History) :=
  ∃ site, Point inside root.shape w h site u middle

theorem source_covered {native inside : ChildPoints} {Good : History → World → Prop}
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (root : Root) {result : Result root.Result} (before : Carrier h w)
    (performed : runPrefix root.action w h = (result,last)) :
    Execution root.shape w h result last ∧
    ∀ site u middle, Point native root.shape w h site u middle →
      Point inside root.shape w h site u middle ∧ Good middle u ∧
      ∃ rest, Residual children root.shape w h site u middle rest ∧
        runPrefix rest u middle = (result,last) := by
  refine ⟨root_cases root performed,?_⟩
  intro site u middle point
  have covered := point.coverage children
  obtain ⟨rest,residual⟩ := point.residual children
  exact ⟨covered,covered.safe carrierGood children before,rest,residual,residual.run.symm.trans performed⟩

/-- These are the two honest phases used by the concrete purge source. -/
def Evidence (h : History) (w : World) : Prop := Carrier h w ∨ Purge.Awaiting h w

noncomputable def evidence_contracts {raw : Zero.RawPoints} {native inside : ChildPoints}
    (repayment : Zero.ReleaseContract raw Evidence)
    (release : ∀ peer, ChildSourceContract (children raw native) (children raw inside) Evidence (.release peer))
    (send : ∀ pid, ChildSourceContract (children raw native) (children raw inside) Evidence (.flushedSend pid))
    (keepalive : ∀ pid, ChildSourceContract (children raw native) (children raw inside) Evidence (.keepalive pid)) :
    ChildContracts (children raw native) (children raw inside) Evidence :=
  contracts (fun _ _ => Or.inl) (fun _ _ => Or.inr) repayment release send keepalive

/-- In the timer caller the queued subtree cannot invoke flushedSend. -/
def timerOther (release : WorkService.Points.ReleasePoints)
    (keepalive : PeerId → World → History → World → History → Prop) : ChildPoints :=
  fun token w h u middle => match token with
  | .release peer => release peer w h u middle
  | .keepalive pid => keepalive pid w h u middle
  | _ => False

noncomputable def timer_contracts {raw : Zero.RawPoints} {releaseNative releaseInside : WorkService.Points.ReleasePoints}
    {keepaliveNative keepaliveInside : PeerId → World → History → World → History → Prop}
    (carrierGood : ∀ h w, Carrier h w → Good h w)
    (pendingGood : ∀ h w, Purge.Awaiting h w → Good h w)
    (repayment : Zero.ReleaseContract raw Good)
    (release : ∀ peer, ChildSourceContract (children raw (timerOther releaseNative keepaliveNative))
      (children raw (timerOther releaseInside keepaliveInside)) Good (.release peer))
    (keepalive : ∀ pid, ChildSourceContract (children raw (timerOther releaseNative keepaliveNative))
      (children raw (timerOther releaseInside keepaliveInside)) Good (.keepalive pid)) :
    ChildContracts (children raw (timerOther releaseNative keepaliveNative))
      (children raw (timerOther releaseInside keepaliveInside)) Good :=
  contracts carrierGood pendingGood repayment release (fun _ => {
    remainder := fun _ _ _ _ point => False.elim point
    continuation := fun _ _ _ _ point => False.elim point
    coverage := fun _ _ _ _ point => False.elim point
    safe := fun _ _ _ _ _ point => False.elim point }) keepalive
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
