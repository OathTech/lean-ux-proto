import Leanux.Proofs.WG.TimerDiscipline.JitterRecords

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

def missingJitterDraw (site : JitterSite) : Stop :=
  .hidden s!"no record left for {site.hiddenSite.info.label}"

theorem hiddenJitter_empty (site : JitterSite) (w : World) (records : w.hidden = some []) :
    (hidden site.hiddenSite).run w = .error (missingJitterDraw site) := by
  cases site <;>
    simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      records, JitterSite.hiddenSite, HiddenSite.info, Worker.sectionId, Worker.index,
      Except.pure, Except.bind, missingJitterDraw]
  all_goals rfl

theorem jitterStep_empty (site : JitterSite) (turn : Nat) (w : World)
    (records : w.hidden = some []) :
    (jitterStep site.hiddenSite turn (none, ())).run w = .error (missingJitterDraw site) := by
  rw [jitterStep, StateT.run_bind, hiddenJitter_empty site w records]
  rfl

theorem jitterLoop_exhausted (site : JitterSite) (rejected : List UInt8)
    (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (turns : List Nat) (enough : rejected.length < turns.length)
    (w : World) (records : w.hidden = some (rejected.map (jitterRecord site))) :
    (jitterLoop site.hiddenSite turns).run w = .error (missingJitterDraw site) := by
  induction rejected generalizing turns w with
  | nil =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      simp only [List.map_nil] at records
      simp only [jitterLoop, List.forIn_cons, StateT.run_bind]
      rw [jitterStep_empty site turn w records]
      rfl
  | cons byte bytes ih =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      simp only [jitterLoop, List.forIn_cons, StateT.run_bind]
      rw [jitterStep_rejected site byte (bytes.map (jitterRecord site)) turn w records
        (bad byte (by simp))]
      exact ih (fun b member => bad b (by simp [member])) turns (by simpa using enough)
        { w with hidden := some (bytes.map (jitterRecord site)) } rfl

theorem jitter_exhausted (site : JitterSite) (rejected : List UInt8)
    (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (w : World) (records : w.hidden = some (rejected.map (jitterRecord site))) :
    (jitterBelowRekeyTimeout site.hiddenSite).run w = .error (missingJitterDraw site) := by
  have budget : recordBudget.run w = .ok (rejected.length + 1, w) := by
    simp [recordBudget, StateT.run, bind, pure, get, getThe, MonadStateOf.get,
      StateT.bind, StateT.pure, StateT.get, Except.bind, Except.pure, records]
  have loop : (forIn ([:rejected.length + 1] : Std.Legacy.Range) (none, ())
      (jitterStep site.hiddenSite)).run w = .error (missingJitterDraw site) := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    apply jitterLoop_exhausted site rejected bad _ _ w records
    simp
  rw [jitter_source, StateT.run_bind, budget]
  change ((do
    let state ← forIn ([:rejected.length + 1] : Std.Legacy.Range) (none, ()) (jitterStep site.hiddenSite)
    jitterFinish state).run w) = _
  rw [StateT.run_bind, loop]
  rfl

end Leanux.Proofs.WG.TimerDiscipline
