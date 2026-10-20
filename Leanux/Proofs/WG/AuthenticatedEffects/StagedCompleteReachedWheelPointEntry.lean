import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWheelPointShape

/-! The outer read is retained as an actual successful source prerequisite.
It supplies the cached packet fields used by every later wheel boundary. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev source (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64) (unit : Option Nat) :
    PrefixM Event Unit := wg (placeOnWheel pid timer expires clock unit)

theorem source_bind (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64) (unit : Option Nat) :
    source pid timer expires clock unit =
      (wg (getPeer pid) >>= fun saved => wg (body pid timer expires clock unit saved)) := by
  unfold source
  rw [source_factor,wg_bind]

theorem read_normal (run : runPrefix (wg (getPeer pid)) w h = (.ok (saved,u),middle)) :
    middle = h ∧ u = w ∧ Cache pid saved u.wg := by
  rw [native_run] at run
  cases actual : ((getPeer pid).run w.wg).run w.ambient with
  | error reason => simp only [actual] at run; cases run
  | ok out =>
    obtain ⟨⟨p,v⟩,ambient⟩ := out
    simp only [actual,Prod.mk.injEq,Except.ok.injEq] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    have same := Peers.getPeer_current pid w.wg v p w.ambient ambient actual
    have cache := read_cache actual
    rcases same with ⟨rfl,rfl,_⟩
    exact ⟨rfl,rfl,cache.2⟩

inductive SourceSite where
  | entry
  | reading
  | body (site : Site)

inductive SourcePoint (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64) (unit : Option Nat) :
    World → History → SourceSite → World → History → Prop where
  | entry : SourcePoint pid timer expires clock unit w h .entry w h
  | reading {w : World} (point : ReadAccess.Point (ReadAccess.peerShape pid) w.wg w.ambient v b) :
      SourcePoint pid timer expires clock unit w h .reading {w with wg:=v,ambient:=b} h
  | body (read : runPrefix (wg (getPeer pid)) w h = (.ok (saved,v),before))
      (point : Point (bodyShape pid timer expires clock unit saved) v before site u middle) :
      SourcePoint pid timer expires clock unit w h (.body site) u middle

theorem SourcePoint.frame (point : SourcePoint pid timer expires clock unit w h site u middle) :
    middle = h ∧ StagedEntry.view u.wg = StagedEntry.view w.wg := by
  cases point with
  | entry => exact ⟨rfl,rfl⟩
  | reading point => exact ⟨rfl,point.frame⟩
  | body read point =>
    have first := read_normal read
    have rest := point.frame first.2.2
    exact ⟨rest.1.trans first.1,by rw [rest.2.1,first.2.1]⟩

theorem SourcePoint.accounted (point : SourcePoint pid timer expires clock unit w h site u middle)
    (before : CompleteCarrier.Accounted h ledger debts locals w.wg) :
    CompleteCarrier.Accounted middle ledger debts locals u.wg := by
  have same := point.frame
  rw [same.1]
  exact before.same_view same.2

theorem SourcePoint.carrier (point : SourcePoint pid timer expires clock unit w h site u middle)
    (before : Consume.Leaf.Carrier h w) : Consume.Leaf.Carrier middle u := by
  obtain ⟨ledger,before⟩ := before
  exact ⟨ledger,point.accounted before⟩

inductive SourceResidual (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64) (unit : Option Nat) :
    World → History → SourceSite → World → History → PrefixM Event Unit → Prop where
  | entry : SourceResidual pid timer expires clock unit w h .entry w h (source pid timer expires clock unit)
  | reading {w : World} (point : ReadAccess.Point (ReadAccess.peerShape pid) w.wg w.ambient v b) :
      SourceResidual pid timer expires clock unit w h .reading {w with wg:=v,ambient:=b} h
        (readRemainder h point >>= fun saved=>wg (body pid timer expires clock unit saved))

  | body (read : runPrefix (wg (getPeer pid)) w h = (.ok (saved,v),before))
      (remaining : Residual (bodyShape pid timer expires clock unit saved) v before site u middle remainder) :
      SourceResidual pid timer expires clock unit w h (.body site) u middle remainder

theorem SourceResidual.run (cut : SourceResidual pid timer expires clock unit w h site u middle remainder) :
    runPrefix (source pid timer expires clock unit) w h = runPrefix remainder u middle := by
  cases cut with
  | entry => rfl
  | reading point => rw [source_bind,runPrefix_bind,runPrefix_bind,readRemainder_run h point]
  | body read remaining => rw [source_bind,runPrefix_bind,read]; exact remaining.run

theorem SourcePoint.residual (point : SourcePoint pid timer expires clock unit w h site u middle) :
    ∃ remainder, SourceResidual pid timer expires clock unit w h site u middle remainder := by
  cases point with
  | entry => exact ⟨_,.entry⟩
  | reading point => exact ⟨_,.reading point⟩
  | body read point => obtain ⟨remaining,source⟩ := point.residual; exact ⟨_,.body read source⟩

theorem SourceResidual.point (cut : SourceResidual pid timer expires clock unit w h site u middle remainder) :
    SourcePoint pid timer expires clock unit w h site u middle := by
  cases cut with
  | entry => exact .entry
  | reading point => exact .reading point
  | body read remaining => exact .body read remaining.point

inductive SourceExecution (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64) (unit : Option Nat) :
    World → History → Result Unit → History → Prop where
  | readStopped (read : runPrefix (wg (getPeer pid)) w h = (.error reason,last)) :
      SourceExecution pid timer expires clock unit w h (.error reason) last
  | body (read : runPrefix (wg (getPeer pid)) w h = (.ok (saved,v),before))
      (execution : Execution (bodyShape pid timer expires clock unit saved) v before result last) :
      SourceExecution pid timer expires clock unit w h result last

theorem SourceExecution.run (execution : SourceExecution pid timer expires clock unit w h result last) :
    runPrefix (source pid timer expires clock unit) w h = (result,last) := by
  rw [source_bind,runPrefix_bind]
  cases execution with
  | readStopped read => rw [read]
  | body read execution => rw [read]; exact execution.run

theorem source_cases (performed : runPrefix (source pid timer expires clock unit) w h = (result,last)) :
    SourceExecution pid timer expires clock unit w h result last := by
  rw [source_bind,runPrefix_bind] at performed
  cases read : runPrefix (wg (getPeer pid)) w h with
  | mk answer before =>
    cases answer with
    | error reason =>
      simp only [read,Prod.mk.injEq] at performed
      rcases performed with ⟨rfl,rfl⟩
      exact .readStopped read
    | ok output =>
      obtain ⟨saved,v⟩ := output
      simp only [read] at performed
      exact .body read (execution_cases _ performed)

theorem source_execution_iff : SourceExecution pid timer expires clock unit w h result last ↔
    runPrefix (source pid timer expires clock unit) w h = (result,last) :=
  ⟨SourceExecution.run,source_cases⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
