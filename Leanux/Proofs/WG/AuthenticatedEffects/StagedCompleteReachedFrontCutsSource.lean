import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrimPointsSource

/-! Fixed routed-front positions retain the original input marker, overflow
receipt and enclosing routed receipt. Native continuations never replace
either receipt's original entry world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.FrontCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Transmit Transmit.Front Transmit.Front.Residual
abbrev History := List Event

def resume (input : Input) (origin : WGWorld) (clock : Ambient)
    (remaining : WGPrefix Event (Except Int PeerId)) : WGPrefix Event (Except Int PeerId) :=
  receiptWGObserved remaining (fun run=>StagedAdmission.Front.routedEvent input
    {run with before:=origin,ambientBefore:=clock})

theorem resume_run
    (continued : runWGPrefix (Transmit.body input) w a (inputHistory input h)=
      runWGPrefix remaining v b middle) :
    runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h=
      runWGPrefix (resume input w a remaining) v b middle := by
  rw [Transmit.front_run,continued,resume,runWGPrefix_receiptWGObserved]
  cases runWGPrefix remaining v b middle with
  | mk result last=>cases result with
    | error stop=>rfl
    | ok out=>obtain ⟨⟨value,u⟩,c⟩:=out; rfl

theorem bind_run_equal {left right : WGPrefix Event α} (next : α → WGPrefix Event β)
    (equal : runWGPrefix left w a h=runWGPrefix right v b middle) :
    runWGPrefix (left >>= next) w a h=runWGPrefix (right >>= next) v b middle := by
  change runStatePrefix (_ >>= _) _ _ _=runStatePrefix (_ >>= _) _ _ _
  rw [runStatePrefix_bind,runStatePrefix_bind]
  change runStatePrefix left w a h=runStatePrefix right v b middle at equal
  rw [equal]

def trimResume (pid : PeerId) (origin : WGWorld) (clock : Ambient)
    (remaining : WG.M Unit) : WGPrefix Event Unit :=
  receiptWGObserved (liftWGPrefix remaining) (fun run=>Event.stagedDisposal
    (.overflow pid {run with before:=origin,ambientBefore:=clock}))

theorem trim_resume_run
    (continued : ((xmitTrim pid).run w).run a=(remaining.run v).run b) :
    runWGPrefix (StagedAdmission.Front.ops.trim pid) w a h=
      runWGPrefix (trimResume pid w a remaining) v b h := by
  rw [StagedAdmission.Front.trim_run,continued,trimResume,runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  cases (remaining.run v).run b with
  | error stop=>rfl
  | ok out=>obtain ⟨⟨value,u⟩,c⟩:=out; rfl

theorem after_trim
    (performed : ((xmitTrim pid).run w).run a=.ok (((),v),b)) :
    runWGPrefix (resolve input (.splice pid packets)) w a h=
      runWGPrefix (do liftWGPrefix (xmitSplice pid packets); pure (.ok pid))
        v b (overflowHistory pid w v a b h) := by
  rw [splice_resolve_run performed]
  change _=runStatePrefix (_ >>= _) _ _ _
  rw [runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift]
  cases ((xmitSplice pid packets).run v).run b with
  | error stop=>rfl
  | ok out=>obtain ⟨⟨value,u⟩,c⟩:=out; cases value; rfl

inductive Point (input : Input) (w : WGWorld) (a : Ambient) (h : History) :
    WGWorld → Ambient → History → Prop where
  | entry : Point input w a h w a h
  | inputMarked : Point input w a h w a (inputHistory input h)
  | selected (path : Selected input (inputHistory input h) w a decision v b) :
      Point input w a h v b (inputHistory input h)
  | trim (selected : Selected input (inputHistory input h) w a (.splice pid packets) q c)
      (point : TrimPoints.Point pid q c v b) : Point input w a h v b (inputHistory input h)
  | trimRecorded (selected : Selected input (inputHistory input h) w a (.splice pid packets) q c)
      (performed : ((xmitTrim pid).run q).run c=.ok (((),v),b)) :
      Point input w a h v b (overflowHistory pid q v c b (inputHistory input h))
  | spliced (selected : Selected input (inputHistory input h) w a (.splice pid packets) q c)
      (trim : ((xmitTrim pid).run q).run c=.ok (((),u),d))
      (splice : ((xmitSplice pid packets).run u).run d=.ok (((),v),b)) :
      Point input w a h v b (overflowHistory pid q u c d (inputHistory input h))
  | preReceipt (path : Transmit.Path input h w a value v b middle) : Point input w a h v b middle

theorem Point.remaining (point : Point input w a h v b middle) :
    ∃remaining,runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h=
      runWGPrefix remaining v b middle := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | inputMarked=>exact ⟨_,resume_run rfl⟩
  | selected path=>exact ⟨_,resume_run path.continuation⟩
  | trim selected point=>
      obtain ⟨remaining,continued⟩:=point.remaining
      apply Exists.intro (resume input w a
        (do trimResume _ _ _ remaining; liftWGPrefix (xmitSplice _ _); pure (.ok _)))
      apply resume_run
      rw [selected.continuation,resolve_splice]
      exact bind_run_equal _ (trim_resume_run continued)
  | trimRecorded selected performed=>exact ⟨_,resume_run (selected.continuation.trans (after_trim performed))⟩
  | spliced selected trim splice=>exact ⟨_,(selected_splice selected trim splice).recorded⟩
  | preReceipt path=>exact ⟨_,path.recorded⟩

inductive RootPoint (input : Input) (w : World) (h : History) : World → History → Prop where
  | source (point : Point input w.wg w.ambient h v b middle) :
      RootPoint input w h {w with wg:=v,ambient:=b} middle

theorem RootPoint.remaining (point : RootPoint input w h u middle) :
    ∃remaining,runPrefix (liftWGObserver (CausalJournal.front input.family input.address input.packets input.mtu)) w h=
      runPrefix remaining u middle := by
  cases point with
  | source point=>
      obtain ⟨remaining,continued⟩:=point.remaining
      refine ⟨liftWGObserver remaining,?_⟩
      rw [liftWGObserver_run,liftWGObserver_run,continued]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.FrontCuts
