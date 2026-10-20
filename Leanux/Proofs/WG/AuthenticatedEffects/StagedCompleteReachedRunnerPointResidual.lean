import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointContract

/-! Remainders are built by induction on the fixed source point. An arbitrary
monadic factor equation is only a consequence, never a reachability premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal

variable {native inside : ChildPoints} {Good : History→World→Prop}

inductive Residual (children : ChildContracts native inside Good) :
    {α : Type} → {action : PrefixOuter Event α} → Shape action → History → Site → World → History →
    PrefixOuter Event α → Prop where
  | nativeEntry (token : Native action) :
      Residual children (.native token) h .entry token.input h action
  | nativeReturn (token : Native action) (performed : runPrefixOuter action h=(.ok out,last)) :
      Residual children (.native token) h .returned (token.output out) last (pure out)
  | stored (point : PrefixStore.Point source w h u middle) :
      Residual children (.native (.stored index w source)) h .stored u middle
        (runAtPrefix index u (PrefixStore.remainder point))
  | prefill (point : PrefixStore.Point (PrefixStore.prefillShape count) w h u middle) :
      Residual children (.native (.prefill count w)) h .prefill u middle
        (do let out ← runAtPrefix 0 u (PrefixStore.remainder point);pure out.2)
  | boot (point : PrefixStore.Point (PrefixStore.bootShape net foreign) w h u middle) :
      Residual children (.native (.boot net foreign w)) h .boot u middle
        (do let out ← runAtPrefix 0 u (PrefixStore.remainder point);pure out.2)
  | cleanup (point : ProductMetadata.Point ProductMetadata.cleanupShape w u) :
      Residual children (.native (.cleanup index w)) h .cleanup u h
        (runAtPrefix index u (ProductMetadata.remainder h point))
  | childEntry (token : Child action) :
      Residual children (.child index w token) h .entry w h (runAtPrefix index w action)
  | childReturn (token : Child action)
      (performed : runPrefixOuter (runAtPrefix index w action) h=(.ok out,last)) :
      Residual children (.child index w token) h .returned out.2 last (pure out)
  | interior (token : Child action) (point : native _ _ token w h u middle) :
      Residual children (.child index w token) h .interior u middle
        (runAtPrefix index u ((children.at token).remainder w h u middle point))
  | left {body : PrefixOuter Event α} {next : α → PrefixOuter Event β}
      {head : Shape body} (tail : ∀value,Shape (next value))
      (point : Residual children head h site u middle remaining) :
      Residual children (.bind head tail) h (.left site) u middle (remaining >>= next)
  | right {body : PrefixOuter Event α} {next : α → PrefixOuter Event β}
      (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : runPrefixOuter body h=(.ok value,middle))
      (point : Residual children (tail value) middle site u last remaining) :
      Residual children (.bind head tail) h (.right site) u last remaining
  | snapshot (label : Label) (w : World) (body : Shape action) :
      Residual children (.marked label w body) h (.marked label .entry) w h action
  | marked (label : Label) (w : World) (point : Residual children shape h site u middle remaining) :
      Residual children (.marked label w shape) h (.marked label site) u middle remaining

theorem Point.residual (children : ChildContracts native inside Good)
    (point : Point native shape h site u middle) :
    ∃remaining,Residual children shape h site u middle remaining := by
  induction point with
  | nativeEntry token => exact ⟨_,.nativeEntry token⟩
  | nativeReturn token performed => exact ⟨_,.nativeReturn token performed⟩
  | stored point => exact ⟨_,.stored point⟩
  | prefill point => exact ⟨_,.prefill point⟩
  | boot point => exact ⟨_,.boot point⟩
  | cleanup point => exact ⟨_,.cleanup point⟩
  | childEntry token => exact ⟨_,.childEntry token⟩
  | childReturn token performed => exact ⟨_,.childReturn token performed⟩
  | interior token point => exact ⟨_,.interior token point⟩
  | left tail _ ih => obtain ⟨remaining,path⟩ := ih; exact ⟨_,.left tail path⟩
  | right head tail leading _ ih => obtain ⟨remaining,path⟩ := ih; exact ⟨_,.right head tail leading path⟩
  | snapshot label w body => exact ⟨_,.snapshot label w body⟩
  | marked label w _ ih => obtain ⟨remaining,path⟩ := ih; exact ⟨_,.marked label w path⟩

theorem Residual.run {shape : Shape action} (path : Residual children shape h site u middle remaining) :
    runPrefixOuter action h=runPrefixOuter remaining middle := by
  induction path with
  | nativeEntry => rfl
  | nativeReturn _ performed => exact performed
  | stored point => simp only [runAtPrefix_run,PrefixStore.remainder_run point]
  | prefill point =>
      simp only [PrefixStore.prefill_source,runPrefixOuter_bind,runAtPrefix_run,PrefixStore.remainder_run point]
  | boot point =>
      simp only [PrefixStore.boot_source,runPrefixOuter_bind,runAtPrefix_run,PrefixStore.remainder_run point]
  | @cleanup w u index history point =>
      simp only [runAtPrefix_run,ProductMetadata.remainder_run history point]
  | childEntry => rfl
  | childReturn _ performed => exact performed
  | interior token point =>
    simp only [runAtPrefix_run,(children.at token).continuation _ _ _ _ point]
  | left _ _ ih => simp only [runPrefixOuter_bind,ih]
  | right _ _ leading _ ih => rw [runPrefixOuter_bind,leading]; exact ih
  | snapshot => rfl
  | marked _ _ _ ih => exact ih

theorem Residual.point {children : ChildContracts native inside Good} (path : Residual children shape h site u middle remaining) :
    Point native shape h site u middle := by
  induction path with
  | nativeEntry token => exact .nativeEntry token
  | nativeReturn token performed => exact .nativeReturn token performed
  | stored point => exact .stored point
  | prefill point => exact .prefill point
  | boot point => exact .boot point
  | cleanup point => exact .cleanup point
  | childEntry token => exact .childEntry token
  | childReturn token performed => exact .childReturn token performed
  | interior token point => exact .interior token point
  | left tail _ ih => exact .left tail ih
  | right head tail leading _ ih => exact .right head tail leading ih
  | snapshot label w body => exact .snapshot label w body
  | marked label w _ ih => exact .marked label w ih

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
