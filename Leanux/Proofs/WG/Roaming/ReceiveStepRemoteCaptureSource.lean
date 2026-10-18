import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteSource
import Leanux.Proofs.Logged.NativeCapture
import Leanux.Proofs.WG.Origins.HistoryAdapters

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ReceiveStepRemote
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Noise Lifetimes Queues Std.Do

theorem capture_value_erases {E : Type} (observed : PrefixM E Bool)
    (erases : ErasesPrefix observed (liftWG receiveStep)) :
    ErasesPrefix (do let r ← captureObserved observed; pure r.value)
      (liftWG receiveStep) := by
  intro w h
  rw [runPrefix_bind,runPrefix_captureObserved]
  cases actual : runPrefix observed w h with
  | mk result history =>
    cases result with
    | error stop => simpa only [actual,Except.map] using erases w h
    | ok pair =>
      obtain ⟨value,current⟩ := pair
      simpa only [actual,Except.map,runPrefix_pure] using erases w h

theorem capture_complete {E : Type} (observed : PrefixM E Bool)
    (erases : ErasesPrefix observed (liftWG receiveStep))
    (w : World) (h : List E) (r : RunWitness Bool) (v : World) (k : List E)
    (run : runPrefix (captureObserved observed) w h = (.ok (r,v),k)) :
    r.before = w ∧ r.after = v ∧ r.Valid (liftWG receiveStep) ∧
      ∃ q : Observation, Matches r q ∧ q.Facts := by
  rw [runPrefix_captureObserved] at run
  cases actual : runPrefix observed w h with
  | mk result history =>
    rw [actual] at run
    cases result with
    | error stop => cases run
    | ok pair =>
      obtain ⟨value,current⟩ := pair
      cases run
      have real : (liftWG receiveStep).run w = .ok (value,v) :=
        (erases w h).symm.trans (congrArg Prod.fst actual)
      exact ⟨rfl,rfl,real,complete ⟨value,w,v⟩ real⟩

theorem original_capture_erases :
    ErasesPrefix (do let r ← captureObserved Origins.HistoryAdapters.receiveStep; pure r.value)
      (liftWG receiveStep) :=
  capture_value_erases _ Origins.HistoryAdapters.receiveStep_erases

theorem original_capture_complete (w : World) (h : List Queues.RxHistory.Event)
    (r : RunWitness Bool) (v : World) (k : List Queues.RxHistory.Event)
    (run : runPrefix (captureObserved Origins.HistoryAdapters.receiveStep) w h = (.ok (r,v),k)) :
    r.before = w ∧ r.after = v ∧ r.Valid (liftWG receiveStep) ∧
      ∃ q : Observation, Matches r q ∧ q.Facts :=
  capture_complete _ Origins.HistoryAdapters.receiveStep_erases w h r v k run

end Leanux.Proofs.WG.Roaming.ReceiveStepRemote
