import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerZeroBorrowFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRawPeerFrames

/-! The zero-key timer's concrete raw repayment family. Its entry evidence
supplies both the original account and the extra reference from the same
timer invocation; no receipt is inserted into this quiet native call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Zero
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

inductive RawPoint (pid : PeerId) (w : World) (h : History) : World → History → Type 1 where
  | lifted (point : RawPeer.Point (some pid) w.wg w.ambient v b) :
      RawPoint pid w h {w with wg:=v,ambient:=b} h

def RawPoint.remainder (point : RawPoint pid w h u middle) : PrefixM Event Unit :=
  match point with
  | .lifted native=>wg native.remainder

theorem RawPoint.continuation (point : RawPoint pid w h u middle) :
    runPrefix (wg (peerPut (some pid))) w h=runPrefix point.remainder u middle := by
  cases point with
  | lifted native=>
    change runPrefix (wg (peerPut (some pid))) w h=runPrefix (wg native.remainder) _ _
    rw [liftWGObserver_run,liftWGObserver_run,runWGPrefix_lift,runWGPrefix_lift,native.continuation]

abbrev rawPoints : RawPoints := fun pid w h u middle=>Nonempty (RawPoint pid w h u middle)

/-- Every declared raw repayment cut conserves the timer's original packet
ledger. The timer's executed borrow prevents this repayment from becoming a
final peer release; its remaining native source is retained exactly. -/
noncomputable def raw_contract (accept : ∀h w,Carrier h w → Good h w) : ReleaseContract rawPoints Good where
  remainder:=fun _ _ _ _ _ point=>(Classical.choice point).remainder
  continuation:=fun _ _ _ _ _ point=>(Classical.choice point).continuation
  safe:=by
    intro pid w h u middle v last before leading point
    have atRepayment:=repayment_entry before leading
    have funded:=repayment_funded leading
    obtain ⟨ledger,account⟩:=atRepayment
    obtain ⟨point⟩:=point
    cases point with
    | lifted native=>exact accept _ _ ⟨ledger,native.accounted account funded⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Zero
