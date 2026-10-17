import Leanux.Proofs.WG.TimerDiscipline.JitterRecordsSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

def missingJitterDraw (site : JitterSite) : Stop :=
  .hidden s!"no record left for {site.hiddenSite.info.label}"

theorem hiddenJitter_empty (site : JitterSite) (g : WGWorld) (w : Ambient)
    (records : w.hidden = some []) :
    ((hidden site.hiddenSite : WG.M (List UInt8)).run g).run w =
      .error (missingJitterDraw site) := by
  have empty : (AmbientM.hidden site.hiddenSite).run w = .error (missingJitterDraw site) := by
    cases site <;>
      simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, StateT.run, bind, pure,
        get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
        records, JitterSite.hiddenSite, HiddenSite.info, Worker.sectionId, Worker.index,
        Except.pure, Except.bind, missingJitterDraw]
    all_goals rfl
  change ((AmbientM.hidden site.hiddenSite).run w >>= fun (value, next) =>
    Except.ok ((value, g), next)) = _
  rw [empty]
  rfl

theorem jitterStep_empty (site : JitterSite) (turn : Nat) (g : WGWorld) (w : Ambient)
    (records : w.hidden = some []) :
    ((jitterStep site.hiddenSite turn (none, ())).run g).run w =
      .error (missingJitterDraw site) := by
  simp only [jitterStep, StateT.run_bind]
  rw [hiddenJitter_empty site g w records]
  rfl

theorem jitterLoop_exhausted (site : JitterSite) (rejected : List UInt8)
    (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (turns : List Nat) (enough : rejected.length < turns.length)
    (g : WGWorld) (w : Ambient)
    (records : w.hidden = some (rejected.map (jitterRecord site))) :
    ((jitterLoop site.hiddenSite turns).run g).run w = .error (missingJitterDraw site) := by
  induction rejected generalizing turns w with
  | nil =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      simp only [List.map_nil] at records
      simp only [jitterLoop, List.forIn_cons, StateT.run_bind]
      rw [jitterStep_empty site turn g w records]
      rfl
  | cons byte bytes ih =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      simp only [jitterLoop, List.forIn_cons, StateT.run_bind]
      rw [jitterStep_rejected site byte (bytes.map (jitterRecord site)) turn g w records
        (bad byte (by simp))]
      exact ih (fun b member => bad b (by simp [member])) turns (by simpa using enough)
        {w with hidden := some (bytes.map (jitterRecord site))} rfl

theorem jitter_exhausted (site : JitterSite) (rejected : List UInt8)
    (bad : ∀ byte ∈ rejected, ¬jitterAccepted byte)
    (g : WGWorld) (w : Ambient)
    (records : w.hidden = some (rejected.map (jitterRecord site))) :
    ((jitterBelowRekeyTimeout site.hiddenSite).run g).run w = .error (missingJitterDraw site) := by
  have budget : ((recordBudget : WG.M Nat).run g).run w =
      .ok ((rejected.length + 1, g), w) := by
    change Except.ok (((match w.hidden with
      | some rs => rs.length + 1
      | none => DOMAIN_FILTER_TURNS), g), w) = _
    simp only [records, List.length_map]
  have loop : ((forIn ([:rejected.length + 1] : Std.Legacy.Range) (none, ())
      (jitterStep site.hiddenSite)).run g).run w = .error (missingJitterDraw site) := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    apply jitterLoop_exhausted site rejected bad _ _ g w records
    simp
  simp only [jitter_source, StateT.run_bind]
  rw [budget]
  change (((do
    let state ← forIn ([:rejected.length + 1] : Std.Legacy.Range) (none, ()) (jitterStep site.hiddenSite)
    jitterFinish state).run g).run w) = _
  simp only [StateT.run_bind]
  rw [loop]
  rfl

end Leanux.Proofs.WG.TimerDiscipline
