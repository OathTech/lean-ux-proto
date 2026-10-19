import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointArmJoin
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumePointNapi

/-! Share the concrete final peer release across receive consumption and NAPI.
The seven receive helpers are source refinements; queued initiation, staging,
wheel placement, transmit and IPv6 remain explicit deeper families. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Composition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def releasePoints (other : Points.ChildPoints) : Points.ChildPoints :=
  fun token w h u middle => match token with
  | .release peer => PeerRetirement.Points.NativePoints peer w h u middle
  | token => other token w h u middle

def consumePoints (leaf : Leaf.ChildPoints) (other : Points.ChildPoints) : Points.ChildPoints :=
  Leaf.consumePoints (Leaf.armPoints leaf) (releasePoints other)

def napiPoints (leaf : Leaf.ChildPoints) (consume : Points.ChildPoints) (other : Napi.Points.ChildPoints) :
    Napi.Points.ChildPoints :=
  Points.napiPoints (consumePoints leaf consume) (PeerRetirement.Points.napiPoints other)

variable {native inside : Leaf.ChildPoints} {nativeOther insideOther : Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints} {Good : History → World → Prop}

noncomputable def release
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (peer : Option PeerId) :
    Points.ChildSourceContract (consumePoints native nativeOther)
      (consumePoints inside insideOther) Good (.release peer) where
  remainder := fun _ _ _ _ point => PeerRetirement.Points.continuation point
  continuation := fun _ _ _ _ point => PeerRetirement.Points.continuation_run point
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before
    exact accept ledger middle u (PeerRetirement.Points.native_evidence accounted point)

structure ReceiveOther (native inside : Leaf.ChildPoints)
    (nativeOther insideOther : Points.ChildPoints) (Good : History → World → Prop) where
  queued : ∀pid,Points.ChildSourceContract (consumePoints native nativeOther)
    (consumePoints inside insideOther) Good (.queued pid)
  staging : ∀pid,Points.ChildSourceContract (consumePoints native nativeOther)
    (consumePoints inside insideOther) Good (.staging pid)

noncomputable def consumeChildren
    (carrierGood : ∀h w,Points.Carrier h w → Good h w)
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (wheel : ∀pid timer expires clock unit,
      Leaf.ChildSourceContract native inside Good (.wheel pid timer expires clock unit))
    (other : ReceiveOther native inside nativeOther insideOther Good) :
    Points.ChildContracts (consumePoints native nativeOther) (consumePoints inside insideOther) Good :=
  Leaf.receive_children carrierGood wheel other.queued other.staging (release accept)

noncomputable def napiRelease
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (peer : Option PeerId) :
    Napi.Points.ChildSourceContract (napiPoints native nativeOther nativeNapi)
      (napiPoints inside insideOther insideNapi) Good (.release peer) where
  remainder := fun _ _ _ _ point => PeerRetirement.Points.continuation point
  continuation := fun _ _ _ _ point => PeerRetirement.Points.continuation_run point
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before
    exact accept ledger middle u (PeerRetirement.Points.native_evidence accounted point)

structure NapiOther (native inside : Leaf.ChildPoints)
    (nativeOther insideOther : Points.ChildPoints) (nativeNapi insideNapi : Napi.Points.ChildPoints)
    (Good : History → World → Prop) where
  transmit : ∀family addr packets mtu,Napi.Points.ChildSourceContract
    (napiPoints native nativeOther nativeNapi) (napiPoints inside insideOther insideNapi) Good
    (.transmit family addr packets mtu)
  receive6 : ∀bytes,Napi.Points.ChildSourceContract
    (napiPoints native nativeOther nativeNapi) (napiPoints inside insideOther insideNapi) Good (.receive6 bytes)

noncomputable def napiChildren
    (carrierGood : ∀h w,Points.Carrier h w → Good h w)
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (wheel : ∀pid timer expires clock unit,
      Leaf.ChildSourceContract native inside Good (.wheel pid timer expires clock unit))
    (receive : ReceiveOther native inside nativeOther insideOther Good)
    (other : NapiOther native inside nativeOther insideOther nativeNapi insideNapi Good) :
    Napi.Points.ChildContracts (napiPoints native nativeOther nativeNapi)
      (napiPoints inside insideOther insideNapi) Good :=
  Points.napi_children carrierGood (consumeChildren carrierGood accept wheel receive)
    (napiRelease accept) other.transmit other.receive6

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Composition
