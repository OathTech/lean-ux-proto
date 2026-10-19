import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateCompositionKey

/-! The refused creation's literal loop entry and ordered cursor. These
source witnesses contain actual original runs, with no accounting premise
and no freely chosen decomposition of an extensionally equal action. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateCleanup
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open AllocatedObligation CreateDisposal CompleteCarrier
open HandshakeSecurity.StagedConservation

inductive Entry (pid : PeerId) (items : List SkbId) (w : World) (h : List Event) :
    Int → World → List Event → Type where
  | reached {first : SkbId} {ret : Int} {u v : World} {middle last : List Event}
      (head : items.head?=some first)
      (admitted : runPrefix (Admission.actual pid items) w h=(.ok (ret,u),middle))
      (repaid : runPrefix (beforeFree pid first ret) u middle=(.ok (true,v),last)) :
      Entry pid items w h ret v last

theorem Entry.residual (entry : Entry pid items w h ret v last) :
    runPrefix (CreatePoints.body pid items) w h=runPrefix (loop (.createRefused pid ret) items) v last := by
  cases entry with
  | reached head admitted repaid=>
    rw [CreatePoints.body,create_factor,head]
    simp only [runPrefix_bind,admitted,repaid,ite_true]

inductive Cursor (reason : Terminal.Reason) : List SkbId → World → List Event →
    SkbId → List SkbId → World → List Event → Type where
  | here : Cursor reason (skb::rest) w h skb rest w h
  | later {head : SkbId} {rest : List SkbId} {w q u : World} {h prior middle : List Event}
      (completed : runPrefix (free reason head) w h=(.ok ((),q),prior))
      (cursor : Cursor reason rest q prior skb tail u middle) :
      Cursor reason (head::rest) w h skb tail u middle

theorem Cursor.residual (cursor : Cursor reason items w h skb rest u middle) :
    runPrefix (loop reason items) w h=runPrefix (loop reason (skb::rest)) u middle := by
  induction cursor with
  | here=>rfl
  | later completed cursor ih=>rw [loop_cons,runPrefix_bind,completed]; exact ih

theorem Cursor.pending_receipt (cursor : Cursor reason items w h skb rest u middle)
    (native : (liftWG (freeTxSkb skb)).run u=.ok ((),v)) (phase : CleanupPrimitive.Phase) :
    runPrefix (loop reason items) w h=
      runPrefix (do CleanupPrimitive.due phase reason skb u v;loop reason rest)
        v (CleanupPrimitive.current phase u skb middle) := by
  rw [cursor.residual,loop_cons,runPrefix_bind,runPrefix_bind]
  rw [CleanupPrimitive.original_suffix phase reason skb u v middle native]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateCleanup
