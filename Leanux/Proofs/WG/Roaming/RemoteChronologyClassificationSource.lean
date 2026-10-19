import Leanux.Proofs.WG.Roaming.RemoteChronologyBridge
import Leanux.Proofs.WG.Roaming.RemoteChronologyInertSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Logged

theorem setterEffect_selected (setter : Option (PeerId × Remote)) (pid : PeerId) (remote : Remote)
    (selected : setterEffect setter pid = some (some remote)) :
    setter = some (pid,remote) := by
  cases setter with
  | none => cases selected
  | some pair =>
    obtain ⟨target,value⟩ := pair
    by_cases same : pid = target
    · simp only [setterEffect,same,ite_true,Option.some.injEq] at selected
      cases same
      cases selected
      rfl
    · simp only [setterEffect,same,ite_false] at selected
      cases selected

theorem effect_cause (event : RemoteDriver.Event) (pid : PeerId) (remote : Remote)
    (selected : effect event pid = some (some remote)) :
    RemoteDriver.Cause event pid remote := by
  cases event with
  | rx event =>
    cases event with
    | consumed occurrence id stamp receipt =>
      dsimp only [effect] at selected
      split at selected
      next family =>
        have same := Option.some.inj (setterEffect_selected _ pid remote selected)
        exact ⟨congrArg Prod.fst same,congrArg Prod.snd same,family⟩
      next invalid => cases selected
    | _ => cases selected
  | receive run =>
    exact receive_cause run pid remote (setterEffect_selected _ pid remote selected)
  | endpoint run =>
    dsimp only [effect] at selected
    split at selected
    next family =>
      have same := Option.some.inj (setterEffect_selected _ pid remote selected)
      exact ⟨congrArg Prod.fst same,congrArg Prod.snd same,family⟩
    next invalid => cases selected
  | birth receipt =>
    cases result : receipt.result with
    | error code => simp only [effect,result] at selected; cases selected
    | ok born =>
      by_cases same : born = pid <;>
        simp only [effect,result,same,ite_true,ite_false] at selected <;> cases selected

theorem nativeRx_inert {α : Type} (observed : MixedM α) :
    ∀ g ambient h pid,
      (runWGPrefix (RoutingJoint.nativeRx observed) g ambient h).2.filterMap
        (fun e => effect (.rx e) pid) = h.filterMap (fun e => effect (.rx e) pid) :=
  nativeRx_history_inert (fun e pid => effect (.rx e) pid) (fun _ _ => rfl) observed

theorem access_inert {α : Type} (observed : MixedM α) :
    ∀ g ambient h pid,
      (runWGPrefix (RemoteConfiguration.access RemoteDriver.Event.rx RemoteDriver.rxEvent observed)
        g ambient h).2.filterMap (fun e => effect e pid) = h.filterMap (fun e => effect e pid) :=
  configurationAccess_history_inert effect RemoteDriver.Event.rx RemoteDriver.rxEvent
    (fun _ _ => rfl) observed

theorem focused_mixed_inert {α : Type} (observed : MixedM α) :
    ∀ w h pid,
      (runPrefix (RemoteDriver.focus (RxHistory.mixed (liftWGObserver observed))) w h).2.filterMap
        (fun e => effect e pid) = h.filterMap (fun e => effect e pid) := by
  apply focused_history_inert effect RemoteDriver.Event.rx RemoteDriver.rxEvent
    (RxHistory.mixed (liftWGObserver observed)) (Appends.focus _ _ _)
  intro w h pid
  rw [← RoutingJoint.nativeRx_product,liftWGObserver_run]
  exact nativeRx_inert observed w.wg w.ambient h pid

theorem focused_origins_inert {α : Type} (observed : PrefixM Origins.Event α) :
    ∀ w h pid,
      (runPrefix (RemoteDriver.focus (Origins.HistoryAdapters.focus observed)) w h).2.filterMap
        (fun e => effect e pid) = h.filterMap (fun e => effect e pid) :=
  focused_history_inert effect RemoteDriver.Event.rx RemoteDriver.rxEvent
    (Origins.HistoryAdapters.focus observed) (Appends.focus _ _ _)
    (historyFocus_history_inert (fun e pid => effect (.rx e) pid)
      (by intro e pid; cases e <;> rfl) observed)

theorem receiveStep_history_inert :
    ∀ w h pid,
      (runPrefix (RemoteDriver.focus Origins.HistoryAdapters.receiveStep) w h).2.filterMap
        (fun e => effect e pid) = h.filterMap (fun e => effect e pid) :=
  focused_origins_inert Origins.HistoryAdapters.localStep

theorem receiveStep_inert_suffix (w : World) (h : List RemoteDriver.Event) :
    ∃ suffix,
      (runPrefix (RemoteDriver.focus Origins.HistoryAdapters.receiveStep) w h).2 = h ++ suffix ∧
      ∀ pid, Untouched effect suffix pid :=
  inert_suffix effect _ (Appends.focus _ _ _) receiveStep_history_inert w h

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
