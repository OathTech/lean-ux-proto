import Leanux.Proofs.WG.Config.CursorReacquireEffects

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The ordered handoff preserves the held-reference invariant for NULL,
equal and distinct cursors. Only the released baseline count must be positive. -/
theorem cursorHeld_step (base current : Device) (old next : Option PeerId)
    (held : CursorHeld base current old)
    (oldData : ∀ id, old = some id → ∃ p, base.peers[id]? = some p ∧ 0 < p.refcount)
    (newData : ∀ id, next = some id → ∃ p, base.peers[id]? = some p) :
    CursorHeld base (cursorHandoff current old next) next := by
  cases old with
  | none =>
    cases next with
    | none => simpa [cursorHandoff,cursorAcquired,cursorReleased] using held
    | some id =>
      obtain ⟨p,found⟩ := newData id rfl
      have actual : current.peers[id]? = some p := by simpa [found] using held.2 id
      constructor
      · simpa [cursorHandoff,cursorAcquired,cursorReleased,actual] using held.1
      · intro key
        by_cases same : id = key
        · subst key
          simp [cursorHandoff,cursorAcquired,cursorReleased,actual,found]
        · simp [cursorHandoff,cursorAcquired,cursorReleased,actual,
            Std.TreeMap.getElem?_insert,same,held.2 key]
  | some old =>
    obtain ⟨p,found,positive⟩ := oldData old rfl
    by_cases same : next = some old
    · subst next
      exact cursorHeld_reacquired base current old p held found
    · apply cursorHeld_handoff base current old next p held found positive
      intro id atNext
      refine ⟨?_,newData id atNext⟩
      intro equal
      subst id
      exact same atNext

/-- Baseline bounds supply the actual acquire-then-release premises, including
the second increment only when the new cursor is already held. -/
theorem cursorHeld_step_ready (base current : Device) (old next : Option PeerId)
    (held : CursorHeld base current old)
    (oldData : ∀ id, old = some id → ∃ p, base.peers[id]? = some p ∧ 0 < p.refcount)
    (newData : ∀ id, next = some id → ∃ p, base.peers[id]? = some p ∧
      0 < p.refcount ∧ p.refcount+1+(if old = some id then 1 else 0) < 2^31) :
    (∀ id, next = some id → ∃ p, current.peers[id]? = some p ∧
      0 < p.refcount ∧ p.refcount+1 < 2^31) ∧
    (∀ id, old = some id → ∃ p, (cursorAcquired current next).peers[id]? = some p ∧
      1 < p.refcount) := by
  constructor
  · intro id atNext
    obtain ⟨p,found,positive,bounded⟩ := newData id atNext
    by_cases same : old = some id
    · refine ⟨{p with refcount := p.refcount+1},?_,?_,?_⟩
      · simpa [found,same] using held.2 id
      · dsimp; omega
      · simpa [same] using bounded
    · refine ⟨p,?_,positive,?_⟩
      · simpa [found,same] using held.2 id
      · simpa [same] using bounded
  · intro id atOld
    obtain ⟨p,found,positive⟩ := oldData id atOld
    have actual : current.peers[id]? = some {p with refcount := p.refcount+1} := by
      simpa [found,atOld] using held.2 id
    cases next with
    | none =>
      refine ⟨{p with refcount := p.refcount+1},?_,?_⟩
      · simpa [cursorAcquired] using actual
      · dsimp; omega
    | some next =>
      by_cases same : next = id
      · subst next
        refine ⟨{p with refcount := p.refcount+1+1},?_,?_⟩
        · simp [cursorAcquired,actual]
        · dsimp; omega
      · obtain ⟨q,resident,_,_⟩ := newData next rfl
        have atNext : current.peers[next]? = some q := by
          simpa [resident,atOld,Ne.symm same] using held.2 next
        refine ⟨{p with refcount := p.refcount+1},?_,?_⟩
        · simp [cursorAcquired,atNext,Std.TreeMap.getElem?_insert,same,actual]
        · dsimp; omega

end Leanux.Proofs.WG.Config
