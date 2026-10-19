import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNestedPeerContinuation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNestedPeerEraseSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteNestedRelease

/-! The nested observer's fixed source points retain actual access histories.
Native release before its counted receipt has explicit pending evidence;
the old resident account is never asserted at that erased-world cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NestedPeer
open Leanux Leanux.WG Leanux.Proofs.Logged
open CausalJournal AllocatedObligation PeerRetirement TransmitSecurity CompleteCarrier

inductive Point (peer : Option PeerId) (w : World) (h : List Event) : World → List Event → Prop where
  | entry : Point peer w h w h
  | stage (site : Stage) (value : site.Result)
      (performed : runWGPrefix (prefixAt actual site peer) w.wg w.ambient h=(.ok ((value,v),b),middle)) :
      Point peer w h {w with wg:=v,ambient:=b} middle
  | erased (value : Cached)
      (performed : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient h=(.ok ((value,v),b),middle)) :
      Point peer w h {w with wg:=v,ambient:=b} middle
  | nativeErase (pid : PeerId) (p : Peer)
      (checked : runWGPrefix (prefixAt actual .checked peer) w.wg w.ambient h=(.ok ((some (pid,p),v),b),middle)) :
      Point peer w h {w with wg:=erasedWorld pid p.staged.length v,ambient:=b} middle
  | recorded (value : Cached)
      (performed : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient h=(.ok ((value,v),b),middle)) :
      Point peer w h {w with wg:=v,ambient:=b}
        (middle++[PeerRelease.receipt peer value w.wg v w.ambient b])
  | finish (pid : PeerId) (p : Peer) (site : Finish.Site)
      (cut : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient h=(.ok ((some (pid,p),v),b),middle))
      (performed : ((Finish.prefixAt site pid p).run v).run b=.ok (((),u),c)) :
      Point peer w h {w with wg:=u,ambient:=c}
        (middle++[PeerRelease.receipt peer (some (pid,p)) w.wg v w.ambient b])

abbrev AccountAt := PeerRetirement.Points.AccountAt

inductive Evidence (ledger : Staged.Obligations.Ledger) (debts : List CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) : List Event → World → Prop where
  | accounted (account : AccountAt ledger debts locals h w.wg) : Evidence ledger debts locals h w
  | pending (peer : Option PeerId) (value : Cached) (origin : World)
      {entryHistory : List Event}
      (before : Accounted entryHistory ledger debts locals origin.wg)
      (native : runWGPrefix (PeerRelease.cut peer) origin.wg origin.ambient entryHistory=(.ok ((value,v),b),middle))
      (after : AccountAt ledger debts locals
        (middle++[PeerRelease.receipt peer value origin.wg v origin.ambient b]) v) :
      Evidence ledger debts locals middle {origin with wg:=v,ambient:=b}
  | nativeErased (peer : Option PeerId) (pid : PeerId) (p : Peer) (origin : World)
      {entryHistory : List Event}
      (before : Accounted entryHistory ledger debts locals origin.wg)
      (checked : runWGPrefix (prefixAt actual .checked peer) origin.wg origin.ambient entryHistory=
        (.ok ((some (pid,p),v),b),middle))
      (after : AccountAt ledger debts locals
        (middle++eraseEvents v pid++[PeerRelease.receipt peer (some (pid,p)) origin.wg
          (erasedWorld pid p.staged.length v) origin.ambient b]) (erasedWorld pid p.staged.length v)) :
      Evidence ledger debts locals middle {origin with wg:=erasedWorld pid p.staged.length v,ambient:=b}

theorem cut_accounted {w : World} (before : Accounted h ledger debts locals w.wg)
    (performed : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient h=(.ok ((value,v),b),middle)) :
    AccountAt ledger debts locals (middle++[PeerRelease.receipt peer value w.wg v w.ambient b]) v := by
  obtain ⟨next,step,frame,_,entry,complete⟩:=
    StagedTerminalComplete.Source.Nested.cut_pair peer before.entry before.complete performed
  exact ⟨next,step,frame,entry,complete⟩

theorem Point.evidence (point : Point peer w h u last) (before : Accounted h ledger debts locals w.wg) :
    Evidence ledger debts locals last u := by
  cases point with
  | entry=>exact .accounted (PeerRetirement.Points.AccountAt.initial before)
  | stage site value performed=>
    exact .accounted (PeerRetirement.Points.AccountAt.initial (stage_accounted before performed))
  | erased value performed=>exact .pending peer value w before performed (cut_accounted before performed)
  | nativeErase pid p checked=>
    exact .nativeErased peer pid p w before checked (cut_accounted before (erased_cut checked))
  | recorded value performed=>exact .accounted (cut_accounted before performed)
  | finish pid p site cut performed=>
    obtain ⟨next,step,frame,account⟩:=cut_accounted before cut
    exact .accounted ⟨next,step,frame,PeerRetirement.Points.finish_accounted account performed⟩

theorem Point.residual (point : Point peer w h u last) :
    ∃remaining,runPrefix (Admission.actualOps.release peer) w h=runPrefix remaining u last := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | stage site value performed=>exact ⟨_,stage_residual performed⟩
  | erased value performed=>exact ⟨_,cut_residual performed⟩
  | nativeErase pid p checked=>exact ⟨_,erased_residual checked⟩
  | recorded value performed=>exact ⟨_,PeerRelease.after_cut peer performed⟩
  | finish pid p site cut performed=>exact ⟨_,finish_residual cut performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NestedPeer
