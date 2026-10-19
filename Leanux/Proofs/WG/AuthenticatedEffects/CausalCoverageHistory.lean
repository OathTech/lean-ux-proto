import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeNested
import Leanux.Proofs.WG.Origins.HistorySupport
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceAcceptance

/-! Protected effects have a current context. Every live candidate in a normal
continuation carries its own successful replay receipt; the poll handles pending
candidates separately so a stopped check cannot grant authority. Delayed-context
root authorization remains a separate strictly earlier occurrence argument. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged

def Protected : Event → Prop
  | .armed _ | .queued _ | .old (.allocated _ _) | .old (.socket _) | .keepalivePrepared _ _ => True
  | _ => False

def Present (history : List Event) : Prop :=
  ∃ token, CausalScope.current scope? history = .ok (some token)

def candidate (position : Nat) (skb : SkbId) (packet : RxPacket) : Event :=
  .scope (.entered ⟨position,.candidate skb packet⟩)

def replay (receipt : TransportDriver.Replay) : Event := .old (.replay receipt)

def Accepted (token : CausalScope.Token Cause) (history : List Event) : Prop :=
  match token.cause with
  | .candidate skb packet => GroOccurrence.Accepted candidate replay ⟨token.position,skb,packet,[]⟩ history
  | _ => True

def Other : Cause → Prop
  | .candidate _ _ => False
  | _ => True

def Candidates (frames : List (CausalScope.Token Cause)) (history : List Event) : Prop :=
  ∀ token ∈ frames, Accepted token history

def Checked (history : List Event) (event : Event) : Prop := Protected event →
  Present history ∧ ∀ token, CausalScope.current scope? history = .ok (some token) → Accepted token history

def Safe (history : List Event) : Prop :=
  ∀ before event after, history = before ++ event :: after → Checked before event

def Inv (frames : List (CausalScope.Token Cause)) (history : List Event) : Prop :=
  Safe history ∧ CausalScope.stack (history.filterMap scope?) = .ok frames ∧ Candidates frames history

theorem Safe.empty : Safe [] := by
  intro before event after position
  have sizes := congrArg List.length position
  simp at sizes

theorem Safe.append (ready : Safe h)
    (checked : ∀ before event after, suffix = before ++ event :: after → Checked (h ++ before) event) :
    Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix ready checked

theorem Safe.emit (ready : Safe h) (checked : Checked h event) : Safe (h ++ [event]) := by
  apply ready.append
  intro before entry after position
  cases before with
  | nil => cases position; simpa only [List.append_nil] using checked
  | cons first rest =>
    have sizes := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega

theorem present (ready : Inv frames h) (live : frames ≠ []) : Present h := by
  cases frames with
  | nil => exact (live rfl).elim
  | cons token rest => exact ⟨token,by simp only [CausalScope.current,ready.2.1,Except.map,List.head?_cons]⟩

theorem Accepted.append (accepted : Accepted token history) (suffix : List Event) :
    Accepted token (history ++ suffix) := by
  cases token with
  | mk index cause =>
    cases cause <;> try exact True.intro
    exact GroOccurrence.accepted_monotone candidate replay _ history suffix accepted

theorem Candidates.append (ready : Candidates frames history) (suffix : List Event) :
    Candidates frames (history ++ suffix) := fun token member => (ready token member).append suffix

theorem current_accepted (ready : Inv frames h) (token : CausalScope.Token Cause)
    (current : CausalScope.current scope? h = .ok (some token)) : Accepted token h := by
  simp only [CausalScope.current,ready.2.1,Except.map] at current
  cases frames with
  | nil => cases current
  | cons first rest =>
    have equal : first = token := by cases current; rfl
    subst first
    exact ready.2.2 token (by simp)

theorem Inv.emit (ready : Inv frames h) (scopeQuiet : scope? event = none)
    (effect : Protected event → frames ≠ []) : Inv frames (h ++ [event]) := by
  refine ⟨ready.1.emit (fun relevant => ⟨present ready (effect relevant),current_accepted ready⟩),?_,
    ready.2.2.append _⟩
  simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,scopeQuiet,
    List.append_nil] using ready.2.1

theorem Inv.quiet (ready : Inv frames h) (suffix : List Event)
    (scopeQuiet : ∀ event ∈ suffix, scope? event = none)
    (effect : ∀ event ∈ suffix, Protected event → frames ≠ []) : Inv frames (h ++ suffix) := by
  induction suffix generalizing h with
  | nil => simpa only [List.append_nil] using ready
  | cons event rest ih =>
    have first := ready.emit (scopeQuiet event (by simp)) (effect event (by simp))
    simpa only [List.append_assoc,List.singleton_append] using
      ih first (fun x hx => scopeQuiet x (by simp [hx])) (fun x hx => effect x (by simp [hx]))

theorem Inv.enter (ready : Inv frames h) (token : CausalScope.Token Cause) (other : Other token.cause) :
    Inv (token :: frames) (h ++ [.scope (.entered token)]) := by
  refine ⟨ready.1.emit (fun impossible => impossible.elim),
    CausalScope.stack_entered scope? Event.scope (fun _ => rfl) h frames token ready.2.1,?_⟩
  intro entry member
  rcases List.mem_cons.mp member with equal | earlier
  · subst entry
    cases token with
    | mk index cause => cases cause <;> first | exact other | exact other.elim
  · exact (ready.2.2 entry earlier).append _

theorem Inv.leave (ready : Inv (token :: frames) h) :
    Inv frames (h ++ [.scope (.exited token.position)]) :=
  ⟨ready.1.emit (fun impossible => impossible.elim),
    CausalScope.stack_exited scope? Event.scope (fun _ => rfl) h frames token ready.2.1,
    fun entry member => (ready.2.2 entry (List.mem_cons_of_mem _ member)).append _⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
