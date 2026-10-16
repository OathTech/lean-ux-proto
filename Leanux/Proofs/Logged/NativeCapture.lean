import Leanux.Proofs.Logged.WGPrefix
import Leanux.Proofs.Logged.Capture

/-! Receipts for actual native WG executions. The two states remain separate,
and an observed capture runs with the incoming journal, including on failure. -/
namespace Leanux.Proofs.Logged
open Leanux

structure WGRunWitness (α : Type) where
  value : α
  before : WGWorld
  after : WGWorld
  ambientBefore : Ambient
  ambientAfter : Ambient

def WGRunWitness.Valid (a : WG.M α) (r : WGRunWitness α) : Prop :=
  (a.run r.before).run r.ambientBefore = .ok ((r.value, r.after), r.ambientAfter)

/-- The inner capture executes the observer once on its actual incoming history. -/
def captureWGObserved (a : WGPrefix E α) : WGPrefix E (WGRunWitness α) :=
  fun wg => do
    let r ← captureObserved (a.run wg)
    return (⟨r.value.1, wg, r.value.2, r.before, r.after⟩, r.value.2)

def captureWGRun (a : WG.M α) : WGPrefix E (WGRunWitness α) :=
  captureWGObserved (liftWGPrefix a)

theorem runWGPrefix_captureWGObserved (a : WGPrefix E α) (wg : WGWorld)
    (ambient : Ambient) (h : List E) :
    runWGPrefix (Logged.captureWGObserved a) wg ambient h =
      ((runWGPrefix a wg ambient h).1.map
        (fun ((x, wg'), ambient') => ((⟨x, wg, wg', ambient, ambient'⟩, wg'), ambient')),
        (runWGPrefix a wg ambient h).2) := by
  unfold runWGPrefix runStatePrefix Logged.captureWGObserved
  dsimp only [StateT.run]
  rw [runPrefix_bind, runPrefix_captureObserved]
  cases hr : runPrefix (a wg) ambient h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out => rcases out with ⟨⟨x, wg'⟩, ambient'⟩; rfl

theorem runWGPrefix_captureWGRun (a : WG.M α) (wg : WGWorld) (ambient : Ambient)
    (h : List E) :
    runWGPrefix (Logged.captureWGRun a) wg ambient h =
      (((a.run wg).run ambient).map
        (fun ((x, wg'), ambient') => ((⟨x, wg, wg', ambient, ambient'⟩, wg'), ambient')), h) := by
  rw [Logged.captureWGRun, runWGPrefix_captureWGObserved, runWGPrefix_lift]

theorem StateAppends.captureWGObserved {a : WGPrefix E α} (ha : StateAppends a) :
    StateAppends (Logged.captureWGObserved a) := by
  intro wg ambient h
  change ∃ suffix, (runWGPrefix (Logged.captureWGObserved a) wg ambient h).2 = h ++ suffix
  rw [runWGPrefix_captureWGObserved]
  exact ha wg ambient h

theorem StateHistoryFrame.captureWGObserved {ρ : E → Option F} {a : WGPrefix E α}
    (ha : StateHistoryFrame ρ a) : StateHistoryFrame ρ (Logged.captureWGObserved a) := by
  intro wg ambient h
  change (runWGPrefix (Logged.captureWGObserved a) wg ambient h).2.filterMap ρ = h.filterMap ρ
  rw [runWGPrefix_captureWGObserved]
  exact ha wg ambient h

/-- The successful receipt retains the actual input history as an execution
witness, and all four native state endpoints. The journal is not reset. -/
theorem StatePrefixEnsures.captureWGObserved
    {P : List E → WGWorld → Ambient → Prop} {S : List E → Prop}
    {Q : α → List E → WGWorld → Ambient → Prop} {a : WGPrefix E α}
    (ha : StatePrefixEnsures P S a Q) :
    StatePrefixEnsures P S (Logged.captureWGObserved a)
      (fun r h wg ambient => r.after = wg ∧ r.ambientAfter = ambient ∧
        Q r.value h r.after r.ambientAfter ∧
        ∃ h0, P h0 r.before r.ambientBefore ∧
          runWGPrefix a r.before r.ambientBefore h0 =
            (.ok ((r.value, r.after), r.ambientAfter), h)) := by
  intro wg ambient h hi
  obtain ⟨suffix, hs, safe, normal⟩ := ha wg ambient h hi
  have hc := runWGPrefix_captureWGObserved a wg ambient h
  simp only [runWGPrefix, runStatePrefix] at hc
  rw [hc]
  refine ⟨suffix, hs, safe, ?_⟩
  cases hr : runPrefix (a.run wg) ambient h with
  | mk result hist =>
    cases result with
    | error e => trivial
    | ok out =>
      rcases out with ⟨⟨x, wg'⟩, ambient'⟩
      have hn : Q x hist wg' ambient' := by
        simpa only [hr] using normal
      simpa only [runWGPrefix, runStatePrefix, hr, Except.map] using
        (show wg' = wg' ∧ ambient' = ambient' ∧ Q x hist wg' ambient' ∧
          ∃ h0, P h0 wg ambient ∧
            runPrefix (a.run wg) ambient h0 = (.ok ((x, wg'), ambient'), hist) from
          ⟨rfl, rfl, hn, h, hi, hr⟩)

theorem StatePrefixPreserves.captureWGObserved
    {I : List E → WGWorld → Ambient → Prop} {S : List E → Prop} {a : WGPrefix E α}
    (ha : StatePrefixPreserves I S a) : StatePrefixPreserves I S (Logged.captureWGObserved a) := by
  apply (StatePrefixEnsures.captureWGObserved ha).consequence (fun _ _ _ h => h)
  intro r h wg ambient hr
  rcases hr with ⟨rfl, rfl, hi, _⟩
  exact hi

theorem StatePrefixEnsures.captureWGRun (a : WG.M α)
    {P : List E → WGWorld → Ambient → Prop} {S : List E → Prop}
    {Q : WGRunWitness α → List E → WGWorld → Ambient → Prop}
    (hs : ∀ h wg ambient, P h wg ambient → S h)
    (hq : ∀ h wg ambient x wg' ambient', P h wg ambient →
      (a.run wg).run ambient = .ok ((x, wg'), ambient') →
      Q ⟨x, wg, wg', ambient, ambient'⟩ h wg' ambient') :
    StatePrefixEnsures P S (Logged.captureWGRun a) Q := by
  intro wg ambient h hi
  have hc := runWGPrefix_captureWGRun a wg ambient h
  simp only [runWGPrefix, runStatePrefix] at hc
  rw [hc]
  refine ⟨[], by simp, hs h wg ambient hi, ?_⟩
  cases hr : (a.run wg).run ambient with
  | error e => trivial
  | ok out =>
    rcases out with ⟨⟨x, wg'⟩, ambient'⟩
    exact hq h wg ambient x wg' ambient' hi hr

theorem captureWGRun_valid (a : WG.M α) :
    StatePrefixEnsures (fun (_ : List E) _ _ => True) (fun _ => True) (Logged.captureWGRun a)
      (fun r _ wg ambient => r.after = wg ∧ r.ambientAfter = ambient ∧ r.Valid a) := by
  apply StatePrefixEnsures.captureWGRun a (fun _ _ _ _ => True.intro)
  intro h wg ambient x wg' ambient' hi hr
  exact ⟨rfl, rfl, hr⟩

/-- Emit one successful receipt after the observed call, with no second call. -/
def receiptWGObserved (a : WGPrefix E α) (receipt : WGRunWitness α → E) : WGPrefix E α := do
  let r ← captureWGObserved a
  emitStatePrefix (receipt r)
  return r.value

theorem runWGPrefix_receiptWGObserved (a : WGPrefix E α) (receipt : WGRunWitness α → E)
    (wg : WGWorld) (ambient : Ambient) (h : List E) :
    runWGPrefix (Logged.receiptWGObserved a receipt) wg ambient h =
      match runWGPrefix a wg ambient h with
      | (.error e, hist) => (.error e, hist)
      | (.ok ((x, wg'), ambient'), hist) =>
        (.ok ((x, wg'), ambient'), hist ++ [receipt ⟨x, wg, wg', ambient, ambient'⟩]) := by
  change runStatePrefix (Logged.receiptWGObserved a receipt) wg ambient h = _
  rw [Logged.receiptWGObserved, runStatePrefix_bind]
  have hc := runWGPrefix_captureWGObserved a wg ambient h
  simp only [runWGPrefix] at hc
  rw [hc]
  simp only [runWGPrefix]
  cases hr : runStatePrefix a wg ambient h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out => rcases out with ⟨⟨x, wg'⟩, ambient'⟩; rfl

theorem StateAppends.receiptWGObserved {a : WGPrefix E α} (ha : StateAppends a)
    (receipt : WGRunWitness α → E) : StateAppends (Logged.receiptWGObserved a receipt) := by
  intro wg ambient h
  change ∃ suffix, (runWGPrefix (Logged.receiptWGObserved a receipt) wg ambient h).2 = h ++ suffix
  obtain ⟨suffix, hs⟩ := ha wg ambient h
  rw [runWGPrefix_receiptWGObserved]
  cases hr : runWGPrefix a wg ambient h with
  | mk result hist =>
    have he : hist = h ++ suffix := by
      simp only [runWGPrefix, runStatePrefix] at hr
      simpa only [hr] using hs
    cases result with
    | error e => exact ⟨suffix, he⟩
    | ok out =>
      rcases out with ⟨⟨x, wg'⟩, ambient'⟩
      exact ⟨suffix ++ [receipt ⟨x, wg, wg', ambient, ambient'⟩], by simp [he]⟩

theorem StateHistoryFrame.receiptWGObserved {ρ : E → Option F} {a : WGPrefix E α}
    (ha : StateHistoryFrame ρ a) (receipt : WGRunWitness α → E)
    (hr : ∀ r, ρ (receipt r) = none) : StateHistoryFrame ρ (Logged.receiptWGObserved a receipt) := by
  intro wg ambient h
  change (runWGPrefix (Logged.receiptWGObserved a receipt) wg ambient h).2.filterMap ρ = h.filterMap ρ
  have he := ha wg ambient h
  rw [runWGPrefix_receiptWGObserved]
  cases ho : runWGPrefix a wg ambient h with
  | mk result hist =>
    have hh : hist.filterMap ρ = h.filterMap ρ := by
      simp only [runWGPrefix, runStatePrefix] at ho
      simpa only [ho] using he
    cases result with
    | error e => exact hh
    | ok out =>
      rcases out with ⟨⟨x, wg'⟩, ambient'⟩
      simpa only [List.filterMap_append, List.filterMap_cons, hr, List.filterMap_nil,
        List.append_nil] using hh

theorem receiptWGObserved_erases {a : WGPrefix E α} {original : WG.M α}
    (ha : ErasesStatePrefix a original) (receipt : WGRunWitness α → E) :
    ErasesStatePrefix (Logged.receiptWGObserved a receipt) original := by
  intro wg ambient h
  change (runWGPrefix (Logged.receiptWGObserved a receipt) wg ambient h).1 = _
  rw [runWGPrefix_receiptWGObserved]
  have he := ha wg ambient h
  cases hr : runWGPrefix a wg ambient h with
  | mk result hist =>
    simp only [runWGPrefix, runStatePrefix] at hr
    simp only [hr] at he
    cases result with
    | error e => exact he
    | ok out => rcases out with ⟨⟨x, wg'⟩, ambient'⟩; exact he

end Leanux.Proofs.Logged
