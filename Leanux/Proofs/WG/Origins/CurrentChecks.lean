import Leanux.Proofs.WG.Origins.CurrentFocus

/-! Positional current-identity checks at actual decrypt and saved-probe cuts.
Equal receipt values at different positions remain separate occurrences.
The existing material/history contract remains an independent conjunct. -/
namespace Leanux.Proofs.WG.CurrentChecks
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
open Origins.HistorySupport (sessions sensitive lifeEncode)

def Checked (pre : List RxHistory.Event) : RxHistory.Event → Prop
  | .rx (.decrypt _ r) => CurrentLifecycle.Inv (sessions pre) r.before
  | .audit (.probe p) => CurrentSessionPrefix.StateInv pre p.world
  | _ => True

def Checks (h : List RxHistory.Event) : Prop :=
  ∀ pre e post, h = pre ++ e :: post → Checked pre e

def Inv (h : List RxHistory.Event) (w : World) : Prop :=
  Origins.HistorySupport.SupportInv h w ∧ CurrentSessionPrefix.StateInv h w ∧ Checks h

def Safe (h : List RxHistory.Event) : Prop :=
  Origins.HistorySupport.HistorySafe h ∧ Checks h

abbrev Preserves (g : RxHistory.Obs α) := PrefixPreserves Inv Safe g

theorem Checks.append (hh : Checks h)
    (hs : ∀ pre e post, s = pre ++ e :: post → Checked (h ++ pre) e) : Checks (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h s hh hs

theorem Checks.snoc (hh : Checks h) (he : Checked h e) : Checks (h ++ [e]) := by
  apply hh.append
  intro pre x post hx
  cases pre with
  | nil =>
    simp only [List.nil_append,List.cons.injEq] at hx
    obtain ⟨rfl,_⟩ := hx
    simpa using he
  | cons y ys => cases ys <;> simp at hx

theorem checked_quiet (he : sensitive e = none) : Checked pre e := by
  cases e <;> try trivial
  case rx r => cases r <;> first | trivial | cases he
  case audit a => cases a <;> first | trivial | cases he

theorem Checks.quiet (hh : Checks h) (hs : s.filterMap sensitive = []) : Checks (h ++ s) := by
  apply hh.append
  intro pre e post he
  apply checked_quiet
  have member : e ∈ s := by rw [he]; simp
  cases selected : sensitive e with
  | none => rfl
  | some value =>
    have found : value ∈ s.filterMap sensitive := List.mem_filterMap.mpr ⟨e,member,selected⟩
    simp [hs] at found

theorem Checks.of_unchanged (appends : Appends g)
    (quiet : ∀ w h, (runPrefix g w h).2.filterMap sensitive = h.filterMap sensitive)
    (hi : Checks h) : Checks (runPrefix g w h).2 := by
  obtain ⟨s,hs⟩ := appends w h
  have eq := quiet w h
  rw [hs,List.filterMap_append] at eq
  have empty : s.filterMap sensitive = [] := by simpa using eq
  rw [hs]
  exact hi.quiet empty

/-- All three proofs refer to the identical actual observer invocation. -/
theorem combine (g : RxHistory.Obs α)
    (material : Origins.HistorySupport.Preserves g) (current : CurrentHistory.Preserves g)
    (checks : ∀ w h, Inv h w → Checks (runPrefix g w h).2) : Preserves g := by
  intro w h hi
  obtain ⟨s,hs,safe,post⟩ := material w h hi.1
  have normal := (current w h hi.2.1).choose_spec.2.2
  have checked := checks w h hi
  refine ⟨s,hs,⟨safe,checked⟩,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    rw [hr] at post normal
    exact ⟨post,normal,checked⟩

theorem quiet (g : RxHistory.Obs α) (appends : Appends g)
    (noSensitive : ∀ w h, (runPrefix g w h).2.filterMap sensitive = h.filterMap sensitive)
    (material : Origins.HistorySupport.Preserves g) (current : CurrentHistory.Preserves g) :
    Preserves g :=
  combine g material current (fun _ _ hi => Checks.of_unchanged appends noSensitive hi.2.2)

/-- The actual session can add lifetime and session receipts, never a decrypt
or probe. Older positional checks keep their exact original prefixes. -/
theorem session (pid : PeerId) : Preserves (Origins.HistoryAdapters.session pid) := by
  apply quiet _ (Appends.focus _ _ _) _ (Origins.HistorySupport.session pid)
    (CurrentSessionPrefix.session pid)
  intro w h
  change (runPrefix (focusPrefix Origins.HistoryAdapters.encode Origins.HistoryAdapters.decode
    (focusPrefix Origins.sessionEncode Origins.sessionDecode
      (liftWGObserver (SessionOrigin.observed pid)))) w h).2.filterMap sensitive = _
  rw [Origins.HistorySupport.focus_compose]
  exact focusPrefix_other _ _ sensitive (by intro e; cases e <;> rfl) _ w h

/-- At this specified decrypt occurrence, support refers only to its strict
earlier session prefix and actual native entry state. -/
theorem Safe.decrypt {id : SkbId} (safe : Safe h)
    (position : h = pre ++ .rx (.decrypt id r) :: post) :
    CurrentLifecycle.Inv (sessions pre) r.before :=
  safe.2 pre (.rx (.decrypt id r)) post position

/-- A saved probe retains the exact prior lifetime projection through the
existing safety conjunct, and current identity at its captured product World. -/
theorem Safe.probe (safe : Safe h)
    (position : h = pre ++ .audit (.probe p) :: post) :
    p.history = RxHistory.prior pre ∧ CurrentSessionPrefix.StateInv pre p.world :=
  ⟨(safe.1.2 pre (.audit (.probe p)) post position).1,
    safe.2 pre (.audit (.probe p)) post position⟩

end Leanux.Proofs.WG.CurrentChecks

