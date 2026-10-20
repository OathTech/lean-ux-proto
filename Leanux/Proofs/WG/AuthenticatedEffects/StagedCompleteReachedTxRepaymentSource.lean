import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNestedPeerPoints
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedKeyAccessAccounted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxCleanupFrames

/-! Shared fixed key and peer repayment cuts for both TX disposal arms.
The original release body and continuation are the same in each arm. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxRepayment
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch HandshakeSecurity.StagedConservation

abbrev action (pid : PeerId) (key : KeypairId) := DeadEntry.repay pid key

theorem ordinary_source (pid : PeerId) (key : KeypairId) :
    CompletionBatch.release cleanupOps pid key=action pid key := rfl

theorem factor (pid : PeerId) (key : KeypairId) : action pid key=(do
    KeyAccess.observed (keypairPutPrefix (some key) false)
    Admission.actualOps.release (some pid)
    pure true) := rfl

inductive Point (pid : PeerId) (key : KeypairId) (w : World) (h : List CausalJournal.Event) :
    World → List CausalJournal.Event → Prop where
  | entry : Point pid key w h w h
  | keyAccess (point : KeyAccess.RootPoint (some key) false w h u middle) : Point pid key w h u middle
  | peer (paid : runPrefix (KeyAccess.observed (keypairPutPrefix (some key) false)) w h=(.ok ((),u),middle))
      (point : NestedPeer.Point (some pid) u middle v last) : Point pid key w h v last
  | returned (performed : runPrefix (action pid key) w h=(.ok (value,u),middle)) : Point pid key w h u middle

theorem Point.remaining (point : Point pid key w h u middle) :
    ∃remaining,runPrefix (action pid key) w h=runPrefix remaining u middle := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | keyAccess point=>
    obtain ⟨remaining,continued⟩:=point.residual
    refine ⟨(do remaining; Admission.actualOps.release (some pid); pure true),?_⟩
    rw [factor,runPrefix_bind,runPrefix_bind,continued]
  | peer paid point=>
    obtain ⟨remaining,continued⟩:=point.residual
    refine ⟨(do remaining; pure true),?_⟩
    rw [factor,runPrefix_bind,paid]
    change runPrefix (Admission.actualOps.release (some pid) >>= fun _=>pure true) _ _=_
    rw [runPrefix_bind,runPrefix_bind,continued]
  | returned performed=>exact ⟨pure _,performed⟩

noncomputable def remainder (point : Point pid key w h u middle) : PrefixM CausalJournal.Event Bool :=
  Classical.choose point.remaining

theorem remainder_run (point : Point pid key w h u middle) :
    runPrefix (action pid key) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxRepayment
