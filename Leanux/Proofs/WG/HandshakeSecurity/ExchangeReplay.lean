import Leanux.Proofs.WG.HandshakeSecurity.ExchangeProgress
import Leanux.Proofs.WG.Origins.HistorySupport

/-! Exact occurrence cuts of the native exchange history. Epochs are indexed
by their original position; projecting a later execution does not renumber an
already consumed exchange. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged

def replayStep (state : Nat × Ledger) (event : Event) : Nat × Ledger :=
  (state.1+1,transition state.1 state.2 event)

def replay (h : List Event) : Ledger :=
  (h.foldl replayStep (0,fun _ => none)).2

private theorem replay_position (h : List Event) (n : Nat) (l : Ledger) :
    (h.foldl replayStep (n,l)).1 = n+h.length := by
  induction h generalizing n l with
  | nil => simp
  | cons event h ih =>
    simp only [List.foldl_cons,replayStep]
    rw [ih]
    simp only [List.length_cons]
    omega

theorem replay_append (h : List Event) (event : Event) :
    replay (h ++ [event]) = transition h.length (replay h) event := by
  simp only [replay,List.foldl_append,List.foldl_cons,List.foldl_nil,replayStep]
  rw [replay_position,Nat.zero_add]

theorem History.replayed {h : List Event} {l : Ledger} (valid : History h l) : replay h = l := by
  induction valid with
  | nil => rfl
  | snoc prior event _ _ ih => rw [replay_append,ih]

theorem History.checked {h : List Event} {l : Ledger} (safe : History h l)
    (pre post : List Event) (event : Event) (position : h = pre ++ event :: post) :
    event.Valid ∧ Allowed (replay pre) event := by
  induction safe generalizing pre post event with
  | nil => cases pre <;> cases position
  | @snoc h l prior next valid enabled ih =>
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
      (fun pre event => event.Valid ∧ Allowed (replay pre) event) h [next]
      (fun pre event post position => ih pre post event position) ?_ pre event post position
    intro before event after single
    cases before with
    | nil => cases single; simpa only [List.append_nil,prior.replayed] using And.intro valid enabled
    | cons x xs =>
      have lengths := congrArg List.length single
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega

private theorem snoc_induction (P : List Event → Prop) (nil : P [])
    (snoc : ∀ h e, P h → P (h ++ [e])) (h : List Event) : P h := by
  have reversed : ∀ xs : List Event, P xs.reverse := by
    intro xs
    induction xs with
    | nil => exact nil
    | cons e xs ih => simpa only [List.reverse_cons] using snoc xs.reverse e ih
  simpa only [List.reverse_reverse] using reversed h.reverse

theorem History.prefix {h : List Event} {l : Ledger} (safe : History h l)
    (pre post : List Event) (position : h = pre ++ post) : History pre (replay pre) := by
  induction pre using snoc_induction generalizing post with
  | nil => exact .nil
  | snoc pre event ih =>
    have split : h = pre ++ event :: post := by simpa only [List.append_assoc,List.singleton_append] using position
    have prior := ih (event :: post) split
    obtain ⟨valid,allowed⟩ := safe.checked pre post event split
    rw [replay_append]
    exact prior.snoc event valid allowed

theorem History.prefix_mono {h : List Event} {l : Ledger} (safe : History h l)
    (pre post : List Event) (position : h = pre ++ post) (pid : PeerId) :
    (replay pre).score pid ≤ l.score pid := by
  induction post using snoc_induction generalizing h l with
  | nil =>
    have same : h = pre := by simpa only [List.append_nil] using position
    subst h
    have result : replay pre = l := by simpa only [List.append_nil] using safe.replayed
    rw [result]
    exact Nat.le_refl _
  | snoc post event ih =>
    have before : History (pre ++ post) (replay (pre ++ post)) :=
      safe.prefix (pre ++ post) [event] (by simpa only [List.append_assoc] using position)
    have enabled := (safe.checked (pre ++ post) [] event
      (by simpa only [List.append_assoc] using position)).2
    have step := transition_mono before.bounded event enabled pid
    have bound := ih before rfl
    have same : l = transition (pre ++ post).length (replay (pre ++ post)) event := by
      rw [← safe.replayed,position,← List.append_assoc,replay_append]
    rw [same]
    exact Nat.le_trans bound step

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
