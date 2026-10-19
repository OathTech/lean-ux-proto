import Leanux.Proofs.Logged.PrefixState
import Leanux.Proofs.Framing.Lift

/-! WireGuard observers run on the mirror's WG and Ambient states. The runner
adapter executes that native observer once and writes back its two outputs. -/
namespace Leanux.Proofs.Logged
open Leanux

abbrev AmbientPrefix (E : Type) := PrefixT E Ambient
abbrev WGPrefix (E : Type) := StateT WGWorld (AmbientPrefix E)

def runWGPrefix (g : WGPrefix E α) (wg : WGWorld) (ambient : Ambient) (h : List E) :
    Except Stop ((α × WGWorld) × Ambient) × List E :=
  runStatePrefix g wg ambient h

def liftWGPrefix (a : WG.M α) : WGPrefix E α := liftStatePrefix a

/-- The only product state here is the runner's actual World. -/
def liftWGObserver (g : WGPrefix E α) : PrefixM E α :=
  fun w => ExceptT.mk fun h =>
    let out := runWGPrefix g w.wg w.ambient h
    (out.1.map (fun ((x, wg), ambient) => (x, { w with wg, ambient })), out.2)

@[simp] theorem runWGPrefix_lift (a : WG.M α) (wg : WGWorld) (ambient : Ambient)
    (h : List E) : runWGPrefix (liftWGPrefix a) wg ambient h = ((a.run wg).run ambient, h) := rfl

theorem liftWGObserver_run (g : WGPrefix E α) (w : World) (h : List E) :
    runPrefix (liftWGObserver g) w h =
      ((runWGPrefix g w.wg w.ambient h).1.map
        (fun ((x, wg), ambient) => (x, { w with wg, ambient })),
        (runWGPrefix g w.wg w.ambient h).2) := rfl

theorem liftWGObserver_erases {g : WGPrefix E α} {a : WG.M α}
    (hg : ErasesStatePrefix g a) : ErasesPrefix (liftWGObserver g) (Leanux.liftWG a) := by
  intro w h
  rw [liftWGObserver_run]
  change ((runPrefix (g.run w.wg) w.ambient h).1.map _) = _
  rw [hg w.wg w.ambient h]
  exact (Leanux.Proofs.Framing.liftWG_run a w).symm

theorem liftWGObserver_bind (g : WGPrefix E α) (f : α → WGPrefix E β) :
    liftWGObserver (g >>= f) = (liftWGObserver g >>= fun x => liftWGObserver (f x)) := by
  funext w h
  change runPrefix (liftWGObserver (g >>= f)) w h =
    runPrefix (liftWGObserver g >>= fun x => liftWGObserver (f x)) w h
  rw [runPrefix_bind, liftWGObserver_run, liftWGObserver_run]
  simp only [runWGPrefix]
  rw [runStatePrefix_bind]
  cases hr : runStatePrefix g w.wg w.ambient h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out => rcases out with ⟨⟨x, wg⟩, ambient⟩; rfl

theorem StatePrefixEnsures.liftWGObserver
    {P : List E → WGWorld → Ambient → Prop} {S : List E → Prop}
    {Q : α → List E → WGWorld → Ambient → Prop} {g : WGPrefix E α}
    (hg : StatePrefixEnsures P S g Q) :
    PrefixEnsures (fun h w => P h w.wg w.ambient) S (liftWGObserver g)
      (fun x h w => Q x h w.wg w.ambient) := by
  intro w h hi
  obtain ⟨suffix, he, hs, hq⟩ := hg w.wg w.ambient h hi
  refine ⟨suffix, he, hs, ?_⟩
  cases hr : runWGPrefix g w.wg w.ambient h with
  | mk result hist =>
    cases result with
    | error e => simp only [liftWGObserver_run, hr, Except.map]
    | ok out =>
      rcases out with ⟨⟨x, wg⟩, ambient⟩
      simp only [runWGPrefix, runStatePrefix] at hr
      simpa only [liftWGObserver_run, runWGPrefix, runStatePrefix, hr, Except.map] using hq

theorem StateAppends.liftWGObserver {g : WGPrefix E α} (hg : StateAppends g) :
    Appends (liftWGObserver g) := fun w h => hg w.wg w.ambient h

theorem StateHistoryFrame.liftWGObserver {ρ : E → Option F} {g : WGPrefix E α}
    (hg : StateHistoryFrame ρ g) : HistoryFrame ρ (liftWGObserver g) :=
  fun w h => hg w.wg w.ambient h

theorem StateProjectsPrefix.liftWGObserver (ρ : E → Option F) (p : α → β)
    {g : WGPrefix E α} {a : WGPrefix F β} (hg : StateProjectsPrefix ρ p g a) :
    ProjectsPrefix ρ p (liftWGObserver g) (liftWGObserver a) := by
  intro w h
  have he := hg w.wg w.ambient h
  change runWGPrefix a w.wg w.ambient (h.filterMap ρ) =
    ((runWGPrefix g w.wg w.ambient h).1.map
      (fun (out, ambient) => (Prod.map p id out, ambient)),
      (runWGPrefix g w.wg w.ambient h).2.filterMap ρ) at he
  rw [liftWGObserver_run, liftWGObserver_run, he]
  cases hr : runWGPrefix g w.wg w.ambient h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out => rcases out with ⟨⟨x, wg⟩, ambient⟩; rfl

end Leanux.Proofs.Logged
