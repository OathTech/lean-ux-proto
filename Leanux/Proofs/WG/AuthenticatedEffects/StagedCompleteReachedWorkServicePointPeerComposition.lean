import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointConsume
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWheelPointPeerComposition

/-! Queued initiation reuses the concrete final peer-release source. Its
canonical tree never calls flushedSend; the source-specific queued contract
therefore requires only the actual repayment family. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Composition
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def queuedPoints : Points.ChildPoints := Points.releasePoints PeerRetirement.Points.NativePoints

noncomputable def queuedRelease {Good : History → World → Prop}
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (peer : Option WG.PeerId) : Points.ChildSourceContract queuedPoints queuedPoints Good (.release peer) where
  remainder := fun _ _ _ _ point => PeerRetirement.Points.continuation point
  continuation := fun _ _ _ _ point => PeerRetirement.Points.continuation_run point
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before
    exact accept ledger middle u (PeerRetirement.Points.native_evidence accounted point)

noncomputable def queuedChildren {Good : History → World → Prop}
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w) :
    Points.ChildContracts queuedPoints queuedPoints Good := Points.release_contracts (queuedRelease accept)

def consumePoints (other : Consume.Points.ChildPoints) : Consume.Points.ChildPoints :=
  Points.consumePoints queuedPoints (Consume.Composition.releasePoints other)

noncomputable def consumeRelease {native inside : Consume.Points.ChildPoints}
    {Good : History → World → Prop}
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (peer : Option WG.PeerId) :
    Consume.Points.ChildSourceContract (consumePoints native) (consumePoints inside) Good (.release peer) where
  remainder := fun _ _ _ _ point => PeerRetirement.Points.continuation point
  continuation := fun _ _ _ _ point => PeerRetirement.Points.continuation_run point
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before
    exact accept ledger middle u (PeerRetirement.Points.native_evidence accounted point)

/-- Receive consumption now derives queued initiation, key/endpoint/timer
helpers, wheel placement and final peer repayment from their fixed sources.
Only staged sending remains an explicit receive child obligation. -/
noncomputable def consumeChildren {native inside : Consume.Points.ChildPoints}
    {Good : History → World → Prop}
    (carrierGood : ∀h w,Points.Carrier h w → Good h w)
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (staging : ∀pid,Consume.Points.ChildSourceContract (consumePoints native) (consumePoints inside) Good (.staging pid)) :
    Consume.Points.ChildContracts (consumePoints native) (consumePoints inside) Good :=
  Points.receive_children carrierGood (queuedChildren accept) staging (consumeRelease accept)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Composition
