import Leanux.Proofs.WG.TransmitSecurity.DriverProjectionBase

/-! Reuse a product observer at a native WG boundary. Only WGWorld and Ambient
exist at that boundary; the synthetic outer components are neither recorded as
native receipts nor exposed in any result claim. Exact erasure requires the
original action to be a lift of the native WG action. -/
namespace Leanux.Proofs.WG.TransmitSecurity.NativeAdapter
open Leanux Leanux.Proofs.Logged Leanux.Proofs.Framing

def world (wg : WGWorld) (ambient : Ambient) : World :=
  {wg,ambient,fs := {},tasks := Runner.initialTasks 0}

def lower (g : PrefixM E α) : WGPrefix E α :=
  fun wg ambient => ExceptT.mk fun h =>
    let out := runPrefix g (world wg ambient) h
    (out.1.map (fun (x,w) => ((x,w.wg),w.ambient)),out.2)

theorem run_lower (g : PrefixM E α) (wg : WGWorld) (ambient : Ambient) (h : List E) :
    runStatePrefix (lower g) wg ambient h =
      ((runPrefix g (world wg ambient) h).1.map (fun (x,w) => ((x,w.wg),w.ambient)),
        (runPrefix g (world wg ambient) h).2) := rfl

theorem lower_erases {g : PrefixM E α} {a : WG.M α}
    (hg : ErasesPrefix g (liftWG a)) : ErasesStatePrefix (lower g) a := by
  intro wg ambient h
  change (runStatePrefix (lower g) wg ambient h).1 = _
  rw [run_lower,hg, liftWG_run]
  dsimp only [world]
  cases (a.run wg).run ambient <;> rfl

theorem lower_lift (a : WG.M α) :
    lower (liftPrefix (liftWG a) : PrefixM E α) = liftWGPrefix a := by
  funext wg ambient h
  change runStatePrefix (lower _) wg ambient h = runStatePrefix (liftWGPrefix a) wg ambient h
  rw [run_lower,runPrefix_lift,liftWG_run]
  change _ = ((a.run wg).run ambient,h)
  dsimp only [world]
  cases (a.run wg).run ambient <;> rfl

theorem lower_projects (ρ : E → Option F) {g : PrefixM E α} {a : PrefixM F α}
    (hg : ProjectsPrefix ρ id g a) : StateProjectsPrefix ρ id (lower g) (lower a) := by
  intro wg ambient h
  change runStatePrefix (lower a) wg ambient (h.filterMap ρ) = _
  rw [run_lower, hg]
  change _ = ((runStatePrefix (lower g) wg ambient h).1.map _, (runStatePrefix (lower g) wg ambient h).2.filterMap ρ)
  rw [run_lower]
  cases hr : runPrefix g (world wg ambient) h with
  | mk result hist => cases result <;> rfl

end Leanux.Proofs.WG.TransmitSecurity.NativeAdapter
