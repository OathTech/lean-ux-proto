import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWheelPointConsume
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointPeerComposition

/-! Wheel placement and peer retirement are derived source contracts at the
receive caller. Queued initiation, staging, transmit and IPv6 remain named. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Composition
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal

noncomputable def wheelConsumeChildren
    {nativeOther insideOther : Points.ChildPoints} {Good : History → World → Prop}
    (carrierGood : ∀h w,Points.Carrier h w → Good h w)
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (other : ReceiveOther Wheel.Points.children Wheel.Points.children nativeOther insideOther Good) :
    Points.ChildContracts (consumePoints Wheel.Points.children nativeOther)
      (consumePoints Wheel.Points.children insideOther) Good :=
  consumeChildren carrierGood accept (Wheel.Points.wheel_contract carrierGood) other

/-- Receive consumption includes the actual endpoint, key, timer, wheel and
peer-release source points. Only its distinct remaining packet families are
assumptions; endpoint preservation is not substituted for their interiors. -/
noncomputable def wheelNapiChildren
    {nativeOther insideOther : Points.ChildPoints}
    {nativeNapi insideNapi : Napi.Points.ChildPoints} {Good : History → World → Prop}
    (carrierGood : ∀h w,Points.Carrier h w → Good h w)
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (receive : ReceiveOther Wheel.Points.children Wheel.Points.children nativeOther insideOther Good)
    (other : NapiOther Wheel.Points.children Wheel.Points.children nativeOther insideOther
      nativeNapi insideNapi Good) :
    Napi.Points.ChildContracts (napiPoints Wheel.Points.children nativeOther nativeNapi)
      (napiPoints Wheel.Points.children insideOther insideNapi) Good :=
  napiChildren carrierGood accept (Wheel.Points.wheel_contract carrierGood) receive other

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Composition
