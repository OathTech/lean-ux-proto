import Leanux.Proofs.WG.Config.RequestWgChainModel
import Leanux.Proofs.WG.Config.RequestOrderEffects

/-! Pure append and position consequences of completed receipt chains. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder.WgLinks
open Leanux Leanux.WG

theorem Chain.snoc {initial current : Campaign2.State} {h : List Receipt}
    (path : Chain initial h current) (r : Receipt) (before : r.before.wg=current) :
    Chain initial (h++[r]) r.after.wg := by
  induction path with
  | nil state=>exact .cons before (.nil _)
  | cons first tail ih=>exact .cons first (ih before)

theorem Before.at {h : List Receipt} (pre : Before h) (state : Campaign2.State) : At h state := by
  intro r member key
  exact False.elim (pre.1 r member key)

theorem Before.safe {h : List Receipt} (pre : Before h) : Safe h := Or.inl pre.1

theorem At.safe {h : List Receipt} {state : Campaign2.State} (pre : At h state) : Safe h :=
  Or.inr ⟨state,pre⟩

theorem At.peer_append {h : List Receipt} {state : Campaign2.State}
    (pre : At h state) (r : Receipt) (p : PeerAttrs) (kind : r.kind=.peer p)
    (before : r.before.wg=state) : At (h++[r]) r.after.wg := by
  intro key member selected
  rcases List.mem_append.mp member with old | new
  · have path:=pre key old selected
    have filtered : peerReceipts (h++[r])=peerReceipts h++[r] := by
      simp [peerReceipts,List.filter_append,kind]
    rw [filtered]
    exact path.snoc r before
  · have same : key=r := List.mem_singleton.mp new
    subst key
    rw [kind] at selected
    cases selected

theorem Before.key_append {h : List Receipt} (pre : Before h) (r : Receipt)
    (kind : r.kind=.keyStage) : At (h++[r]) r.after.wg := by
  intro key member selected
  rcases List.mem_append.mp member with old | new
  · exact False.elim (pre.1 key old selected)
  · have same : key=r := List.mem_singleton.mp new
    subst key
    have filtered : peerReceipts (h++[r])=[] := by
      simp only [peerReceipts_append,pre.2]
      simp [peerReceipts,kind]
    rw [filtered]
    exact .nil _

theorem Before.silent_append {h : List Receipt} (pre : Before h) (r : Receipt)
    (notKey : r.kind≠.keyStage) (notPeer : ∀p,r.kind≠.peer p) : Before (h++[r]) := by
  constructor
  · intro other member key
    rcases List.mem_append.mp member with old | new
    · exact pre.1 other old key
    · have same : other=r := List.mem_singleton.mp new
      subst other
      exact notKey key
  · rw [peerReceipts_append,pre.2,List.nil_append]
    unfold peerReceipts
    cases kind : r.kind <;> simp only [List.filter_cons,List.filter_nil]
    all_goals first | rfl | exact False.elim (notPeer _ kind)

theorem before_nil : Before [] := by
  constructor
  · intro r member; cases member
  · rfl

theorem Before.append {left right : List Receipt} (a : Before left) (b : Before right) :
    Before (left++right) := by
  constructor
  · intro r member key
    rcases List.mem_append.mp member with earlier|later
    · exact a.1 r earlier key
    · exact b.1 r later key
  · rw [peerReceipts_append,a.2,b.2,List.nil_append]

theorem clear_before {attrs : DeviceAttrs} {h : List Receipt} (path : ClearPrefix attrs h) :
    Before h := by
  refine ⟨?_,path.peerReceipts⟩
  intro r member key
  obtain ⟨pid,kind⟩:=path.1 r member
  rw [kind] at key
  cases key

theorem Chain.first {initial final : Campaign2.State} {h : List Receipt}
    (path : Chain initial h final) (r : Receipt) (selected : h[0]?=some r) :
    r.before.wg=initial := by
  cases path with
  | nil state=>simp only [List.getElem?_nil] at selected;cases selected
  | @cons state final first rest before tail=>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
    subst r
    exact before

theorem Chain.adjacent {initial final : Campaign2.State} {h : List Receipt}
    (path : Chain initial h final) (i : Nat) (left right : Receipt)
    (selected : h[i]?=some left) (next : h[i+1]?=some right) :
    left.after.wg=right.before.wg := by
  induction path generalizing i with
  | nil state=>simp only [List.getElem?_nil] at selected;cases selected
  | @cons state final first rest before tail ih=>
    cases i with
    | zero=>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
      subst left
      exact (tail.first right (by simpa using next)).symm
    | succ i=>
      exact ih i (by simpa using selected) (by simpa [Nat.add_assoc] using next)

theorem Chain.last {initial final : Campaign2.State} {h : List Receipt}
    (path : Chain initial h final) (i : Nat) (r : Receipt)
    (selected : h[i]?=some r) (last : i+1=h.length) : r.after.wg=final := by
  induction path generalizing i with
  | nil state=>simp only [List.getElem?_nil] at selected;cases selected
  | @cons state final first rest before tail ih=>
    cases i with
    | zero=>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
      subst r
      have empty : rest=[] := by
        have size : rest.length=0 := by simpa using last.symm
        exact List.length_eq_zero_iff.mp size
      subst rest
      cases tail
      rfl
    | succ i=>
      exact ih i (by simpa using selected) (by simpa using last)

theorem Chain.empty {initial final : Campaign2.State} {h : List Receipt}
    (path : Chain initial h final) (empty : h=[]) : initial=final := by
  subst h
  cases path
  rfl

end Leanux.Proofs.WG.Config.RequestOrder.WgLinks
