import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointPeerComposition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainPointServiceComposition

/-! The scheduled send and clear sources share concrete peer retirement.
The handshake sender remains a distinct source obligation. Canonical source
remainders are transported to services and the original send drain. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.ServiceComposition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def workPoints (other : Points.ChildPoints) : Points.ChildPoints :=
  fun token w h u middle => match token with
  | .release peer => PeerRetirement.Points.NativePoints peer w h u middle
  | .flushedSend pid => other (.flushedSend pid) w h u middle

variable {native inside : Points.ChildPoints} {Good : History → World → Prop}

noncomputable def release
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (peer : Option PeerId) :
    Points.ChildSourceContract (workPoints native) (workPoints inside) Good (.release peer) where
  remainder := fun _ _ _ _ point => PeerRetirement.Points.continuation point
  continuation := fun _ _ _ _ point => PeerRetirement.Points.continuation_run point
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before
    exact accept ledger middle u (PeerRetirement.Points.native_evidence accounted point)

noncomputable def workChildren
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (sender : ∀pid,Points.ChildSourceContract (workPoints native) (workPoints inside) Good (.flushedSend pid)) :
    Points.ChildContracts (workPoints native) (workPoints inside) Good where
  contract := fun token => match token with
    | .release peer => release accept peer
    | .flushedSend pid => sender pid

noncomputable def remainder (root : Points.Root)
    (children : Points.ChildContracts native inside Good)
    (w : World) (h : History) (u : World) (middle : History)
    (point : Points.RootPoint native root w h u middle) : PrefixM Event Unit :=
  Classical.choose ((Classical.choose_spec point).residual children)

theorem remainder_run (root : Points.Root)
    (children : Points.ChildContracts native inside Good)
    (point : Points.RootPoint native root w h u middle) :
    runPrefix root.action w h = runPrefix (remainder root children w h u middle point) u middle :=
  (Classical.choose_spec ((Classical.choose_spec point).residual children)).run

def servicePoints (work : Points.ChildPoints) (other : Service.Points.ChildPoints) :
    Service.Points.ChildPoints := fun α action token w h u middle => match token with
  | .family .sendWorker => Points.RootPoint work .scheduledSend w h u middle
  | .family .clearWorker => Points.RootPoint work .scheduledClear w h u middle
  | token => other α action token w h u middle

noncomputable def sendWorker
    {nativeOther insideOther : Service.Points.ChildPoints}
    (carrierGood : ∀h w,Points.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good) :
    Service.Points.ChildSourceContract (servicePoints native nativeOther)
      (servicePoints inside insideOther) Good (.family .sendWorker) where
  remainder := remainder .scheduledSend children
  continuation := fun _ _ _ _ point => remainder_run .scheduledSend children point
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children before.1

noncomputable def clearWorker
    {nativeOther insideOther : Service.Points.ChildPoints}
    (carrierGood : ∀h w,Points.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good) :
    Service.Points.ChildSourceContract (servicePoints native nativeOther)
      (servicePoints inside insideOther) Good (.family .clearWorker) where
  remainder := remainder .scheduledClear children
  continuation := fun _ _ _ _ point => remainder_run .scheduledClear children point
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children before.1

def drainPoints (work : Points.ChildPoints) (other : SendDrain.Points.ChildPoints) :
    SendDrain.Points.ChildPoints := fun token w h u middle => match token with
  | .worker => Points.RootPoint work .scheduledSend w h u middle
  | token => other token w h u middle

noncomputable def drainWorker
    {nativeOther insideOther : SendDrain.Points.ChildPoints}
    (carrierGood : ∀h w,Points.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good) :
    SendDrain.Points.ChildSourceContract (drainPoints native nativeOther)
      (drainPoints inside insideOther) Good .worker where
  remainder := remainder .scheduledSend children
  continuation := fun _ _ _ _ point => remainder_run .scheduledSend children point
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children before.1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.ServiceComposition
