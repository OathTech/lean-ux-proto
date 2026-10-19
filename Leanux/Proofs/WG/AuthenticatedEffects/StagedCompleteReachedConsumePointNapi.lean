import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumePointCoverage

/-! Structural refinement of the two actual NAPI receive children. The other
three NAPI child families retain their original exact source contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

def napiPoints (inside : ChildPoints) (other : Napi.Points.ChildPoints) : Napi.Points.ChildPoints :=
  fun token w h u middle => match token with
    | .counter skb packet => ∃ site, Point inside (counterReceiptShape skb packet) w h site u middle
    | .consume pid packet endpoint => ∃ site, Point inside (consumeShape pid packet endpoint) w h site u middle
    | token => other token w h u middle

variable {native inside : ChildPoints} {nativeOther insideOther : Napi.Points.ChildPoints}
variable {Good : History → World → Prop}

noncomputable def napi_counter
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (skb : SkbId) (packet : RxPacket) :
    Napi.Points.ChildSourceContract (napiPoints native nativeOther)
      (napiPoints inside insideOther) Good (.counter skb packet) where
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
    exact point.safe carrierGood children before

noncomputable def napi_consume
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint) :
    Napi.Points.ChildSourceContract (napiPoints native nativeOther)
      (napiPoints inside insideOther) Good (.consume pid packet endpoint) where
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
    exact point.safe carrierGood children before

noncomputable def napi_children
    (carrierGood : ∀ h w, Carrier h w → Good h w) (children : ChildContracts native inside Good)
    (release : ∀ peer, Napi.Points.ChildSourceContract (napiPoints native nativeOther)
      (napiPoints inside insideOther) Good (.release peer))
    (transmit : ∀ family addr packets mtu, Napi.Points.ChildSourceContract (napiPoints native nativeOther)
      (napiPoints inside insideOther) Good (.transmit family addr packets mtu))
    (receive6 : ∀ bytes, Napi.Points.ChildSourceContract (napiPoints native nativeOther)
      (napiPoints inside insideOther) Good (.receive6 bytes)) :
    Napi.Points.ChildContracts (napiPoints native nativeOther) (napiPoints inside insideOther) Good where
  counter := napi_counter carrierGood children
  consume := napi_consume carrierGood children
  release := release
  transmit := transmit
  receive6 := receive6

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
