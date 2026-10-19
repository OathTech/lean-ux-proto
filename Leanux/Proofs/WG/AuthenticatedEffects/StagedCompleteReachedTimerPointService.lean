import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointSelection
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointContract

/-! The actual service caller's timer/selected/finished children are replaced
by their canonical timer points, at the same state and original history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

def servicePoints (inside : ChildPoints) (other : Service.Points.ChildPoints) : Service.Points.ChildPoints :=
  fun _ _ token w h u middle => match token with
  | .family (.timer pid timer) => RootPoint inside (.callback pid timer) w h u middle
  | .family (.selected device bound pid timer entry) => RootPoint inside (.selected device bound pid timer entry) w h u middle
  | .family (.finished token) => RootPoint inside (.finished token) w h u middle
  | token => other _ _ token w h u middle

noncomputable def timer_contract {native inside : ChildPoints} {Good : History → World → Prop}
    {nativeOther insideOther : Service.Points.ChildPoints}
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (pid : PeerId) (timer : PeerTimer) : Service.Points.ChildSourceContract (servicePoints native nativeOther)
      (servicePoints inside insideOther) Good (.family (.timer pid timer)) where
  remainder := fun _ _ _ _ point => Classical.choose ((Classical.choose_spec point).residual children)
  continuation := by
    intro w h u middle point
    exact (Classical.choose_spec ((Classical.choose_spec point).residual children)).run
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children before.1

noncomputable def selected_contract {native inside : ChildPoints} {Good : History → World → Prop}
    {nativeOther insideOther : Service.Points.ChildPoints}
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (device : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) : Service.Points.ChildSourceContract (servicePoints native nativeOther)
      (servicePoints inside insideOther) Good (.family (.selected device bound pid timer entry)) where
  remainder := fun _ _ _ _ point => Classical.choose ((Classical.choose_spec point).residual children)
  continuation := by
    intro w h u middle point
    exact (Classical.choose_spec ((Classical.choose_spec point).residual children)).run
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children before.1

noncomputable def finished_contract {native inside : ChildPoints} {Good : History → World → Prop}
    {nativeOther insideOther : Service.Points.ChildPoints}
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (token : Nat) : Service.Points.ChildSourceContract (servicePoints native nativeOther)
      (servicePoints inside insideOther) Good (.family (.finished token)) where
  remainder := fun _ _ _ _ point => Classical.choose ((Classical.choose_spec point).residual children)
  continuation := by
    intro w h u middle point
    exact (Classical.choose_spec ((Classical.choose_spec point).residual children)).run
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children before.1

noncomputable def service_children {native inside : ChildPoints} {Good : History → World → Prop}
    {nativeOther insideOther : Service.Points.ChildPoints}
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (schedule : ∀ stack, Service.Points.ChildSourceContract (servicePoints native nativeOther)
      (servicePoints inside insideOther) Good (.family (.schedule stack)))
    (sends : Service.Points.ChildSourceContract (servicePoints native nativeOther)
      (servicePoints inside insideOther) Good (.family .sends))
    (sendWorker : Service.Points.ChildSourceContract (servicePoints native nativeOther)
      (servicePoints inside insideOther) Good (.family .sendWorker))
    (clearWorker : Service.Points.ChildSourceContract (servicePoints native nativeOther)
      (servicePoints inside insideOther) Good (.family .clearWorker)) :
    Service.Points.ChildContracts (servicePoints native nativeOther) (servicePoints inside insideOther) Good where
  schedule := schedule
  sends := sends
  sendWorker := sendWorker
  clearWorker := clearWorker
  timer := timer_contract carrierGood children
  selected := selected_contract carrierGood children
  finished := finished_contract carrierGood children
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
