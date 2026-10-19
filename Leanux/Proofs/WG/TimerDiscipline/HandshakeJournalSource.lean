import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalBridge
import Leanux.Proofs.WG.TimerDiscipline.HookJournalSource
import Leanux.Proofs.Logged.PrefixState
import Leanux.Proofs.WG.Noise.SessionSource

/-! Execute each original session or hook once. Completed sessions have an exact native run witness; hooks retain original success or Stop. The allocation counter equation is derived from that same session run. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev Obs := WGPrefix Event
def session (pid : PeerId) : Obs Bool :=
  fun g a => ExceptT.mk fun h =>
    match ((beginSession pid).run g).run a with
    | .error stop => (.error stop,h)
    | .ok ((begun,next),inputs) =>
      (.ok ((begun,next),inputs),
        h++[.session ⟨pid,Campaign2.snapshot g a,begun,Campaign2.snapshot next inputs⟩])
def hook (kind : HookJournal.Hook) (pid : PeerId) : Obs Unit :=
  focusStatePrefix Event.hook decodeHook (HookJournal.observed kind pid)
theorem session_exact (pid : PeerId) (g : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (session pid) g a h =
      match ((beginSession pid).run g).run a with
      | .error stop => (.error stop,h)
      | .ok ((begun,next),inputs) =>
        (.ok ((begun,next),inputs),
         h++[.session ⟨pid,Campaign2.snapshot g a,begun,Campaign2.snapshot next inputs⟩]) := rfl
theorem session_erases (pid : PeerId) : ErasesStatePrefix (session pid) (beginSession pid) := by
  intro g a h
  change (runWGPrefix (session pid) g a h).1=_
  rw [session_exact]
  cases ((beginSession pid).run g).run a <;> rfl
theorem hook_exact (kind : HookJournal.Hook) (pid : PeerId) (g : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (hook kind pid) g a h =
      (((HookJournal.action kind pid).run g).run a,
       h++[.hook ⟨kind,pid,Campaign2.snapshot g a,
          Campaign2.observeResult (((HookJournal.action kind pid).run g).run a)⟩]) := by
  change (_, h ++ (((h.filterMap decodeHook) ++ [_]).drop (h.filterMap decodeHook).length).map Event.hook)=_
  simp only [List.drop_left, List.map_cons, List.map_nil]
  rfl
theorem hook_erases (kind : HookJournal.Hook) (pid : PeerId) :
    ErasesStatePrefix (hook kind pid) (HookJournal.action kind pid) :=
  focusStatePrefix_erases _ _ (HookJournal.observed_erases kind pid)
theorem valid_snoc {h : List Event} {e : Event} (prior : ValidHistory h) (fresh : e.Valid) :
    ValidHistory (h++[e]) := by
  intro x member
  rcases List.mem_append.mp member with old|new
  · exact prior x old
  · simp only [List.mem_singleton] at new
    subst x
    exact fresh
theorem session_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (session pid) := by
  intro g a h prior
  dsimp only [runPrefix,session,StateT.run,ExceptT.run,ExceptT.mk]
  cases run : beginSession pid g a with
  | error stop => exact ⟨[],by simp,prior,True.intro⟩
  | ok out =>
    obtain ⟨⟨begun,next⟩,inputs⟩:=out
    have valid := valid_snoc prior (show Event.Valid (.session
      ⟨pid,Campaign2.snapshot g a,begun,Campaign2.snapshot next inputs⟩) from
        ⟨g,a,next,inputs,rfl,rfl,run⟩)
    exact ⟨[_],rfl,valid,valid⟩
theorem hook_valid (kind : HookJournal.Hook) (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (hook kind pid) := by
  intro g a h prior
  have eq:=hook_exact kind pid g a h
  change runPrefix ((hook kind pid).run g) a h=_ at eq
  rw [eq]
  have valid := valid_snoc prior (show Event.Valid (.hook
    ⟨kind,pid,Campaign2.snapshot g a,Campaign2.observeResult (((HookJournal.action kind pid).run g).run a)⟩)
    from HookJournal.fresh_valid kind pid g a)
  refine ⟨[_],rfl,valid,?_⟩
  cases run : ((HookJournal.action kind pid).run g).run a with
  | error _ => trivial
  | ok out =>
    obtain ⟨⟨value,next⟩,inputs⟩:=out
    simpa only [run] using valid
theorem SessionReceipt.Valid.counter {r : SessionReceipt} (valid : r.Valid) :
    r.after.wg.keypairCounter = r.before.wg.keypairCounter + (if r.begun then 1 else 0) := by
  obtain ⟨g,a,next,inputs,before,after,run⟩:=valid
  have resident : ∃d p,g.dev=some d ∧ d.peers[r.pid]?=some p := by
    cases device : g.dev with
    | none =>
      simp [beginSession,getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases peer : d.peers[r.pid]? with
      | none =>
        simp [beginSession,getPeer,getDev,device,peer,invariant,AmbientM.invariant] at run
        cases run
      | some p => exact ⟨d,p,rfl,peer⟩
  obtain ⟨d,p,device,resident⟩:=resident
  obtain ⟨final,_,effect⟩:=Noise.beginSession_effect r.pid d p g.keypairCounter resident
    g a r.begun next inputs ⟨device,rfl⟩ run
  rw [before,after]
  cases begun : r.begun <;> simp only [Noise.SessionEffect,begun,Bool.false_eq_true,ite_false,
    ite_true] at effect ⊢
  · exact effect.2
  · exact effect.2.2.2.1

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
