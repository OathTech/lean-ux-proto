import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointZero
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointPurgeAccounts

/-! Purge and zero expiry are concrete source families. Only actual keepalive,
observed release/sender and the contextual raw zero repayment stay deeper. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

def children (raw : Zero.RawPoints) (other : ChildPoints) : ChildPoints := fun token w h u middle => match token with
  | .purge pid => Purge.Point pid w h u middle
  | .zero pid => Zero.Point raw pid w h u middle
  | _ => other token w h u middle

noncomputable def purge_contract {raw : Zero.RawPoints} {native inside : ChildPoints}
    (carrierGood : ∀ h w, Carrier h w → Good h w)
    (pendingGood : ∀ h w, Purge.Awaiting h w → Good h w) (pid : PeerId) :
    ChildSourceContract (children raw native) (children raw inside) Good (.purge pid) where
  remainder := fun _ _ _ _ point => Purge.remainder point
  continuation := fun _ _ _ _ point => Purge.point_continuation point
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    rcases Purge.point_evidence before point with kept | waiting
    · exact carrierGood _ _ kept
    · exact pendingGood _ _ waiting

noncomputable def zero_contract {raw : Zero.RawPoints} {native inside : ChildPoints}
    (carrierGood : ∀ h w, Carrier h w → Good h w)
    (repayment : Zero.ReleaseContract raw Good) (pid : PeerId) :
    ChildSourceContract (children raw native) (children raw inside) Good (.zero pid) where
  remainder := fun _ _ _ _ point => Zero.remainder repayment point
  continuation := fun _ _ _ _ point => Zero.continuation repayment point
  coverage := fun _ _ _ _ point => point
  safe := fun _ _ _ _ before point => Zero.safe carrierGood repayment before point

noncomputable def contracts {raw : Zero.RawPoints} {native inside : ChildPoints}
    (carrierGood : ∀ h w, Carrier h w → Good h w)
    (pendingGood : ∀ h w, Purge.Awaiting h w → Good h w)
    (repayment : Zero.ReleaseContract raw Good)
    (release : ∀ peer, ChildSourceContract (children raw native) (children raw inside) Good (.release peer))
    (send : ∀ pid, ChildSourceContract (children raw native) (children raw inside) Good (.flushedSend pid))
    (keepalive : ∀ pid, ChildSourceContract (children raw native) (children raw inside) Good (.keepalive pid)) :
    ChildContracts (children raw native) (children raw inside) Good where
  contract := fun token => match token with
    | .release peer => release peer
    | .flushedSend pid => send pid
    | .keepalive pid => keepalive pid
    | .purge pid => purge_contract carrierGood pendingGood pid
    | .zero pid => zero_contract carrierGood repayment pid
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
