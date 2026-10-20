import History

namespace Binary

/-- Evidence attached to a physical segment: the endpoint invariant, actual
observations/history and the required invariant at every appended cut. The
endpoint and cut invariants may differ (for example, a stronger endpoint ABI).
Execution is supplied by Segment below, never inferred from this record. -/
structure SegmentTrace {Error Event : Type}
    (edge : MachineState → MachineState → Except Error (List Event))
    (Cut Frame AtCut : MachineState → Prop) (initialHistory : List MachineState)
    (events : List Event) (current : Executed) : Prop where
  frame : Frame current.machine
  observed : observeHistory edge current.history = .ok events
  last : current.history.getLast? = some current.machine
  extension : ∃ tail, current.history = initialHistory ++ tail ∧ ∀ q ∈ tail, Cut q → AtCut q

namespace SegmentTrace

/-- Cut obligations are discharged once when joining actual suffixes. -/
theorem trans {Error Event : Type} {edge : MachineState → MachineState → Except Error (List Event)}
    {Cut Frame AtCut history events nextEvents current next}
    (first : SegmentTrace edge Cut Frame AtCut history events current)
    (second : SegmentTrace edge Cut Frame AtCut current.history nextEvents next) :
    SegmentTrace edge Cut Frame AtCut history nextEvents next := by
  obtain ⟨a, ha, ca⟩ := first.extension
  obtain ⟨b, hb, cb⟩ := second.extension
  refine ⟨second.frame, second.observed, second.last, a++b,
    by rw [hb, ha, List.append_assoc], ?_⟩
  intro q member cut
  rcases List.mem_append.mp member with left | right
  · exact ca q left cut
  · exact cb q right cut

/-- Lift a proved concrete suffix without rebuilding history splice facts. -/
theorem of_suffix {Error Event : Type} {edge : MachineState → MachineState → Except Error (List Event)}
    {Cut Frame AtCut history events current next}
    (observed : observeHistory edge history = .ok events)
    (last : history.getLast? = some current)
    (tail : List MachineState) (recorded : next.history = history ++ tail)
    (frame : Frame next.machine)
    (lastNext : (current :: tail).getLast? = some next.machine)
    (delta : List Event) (localObserved : observeHistory edge (current :: tail) = .ok delta)
    (cuts : ∀ q ∈ tail, Cut q → AtCut q) :
    SegmentTrace edge Cut Frame AtCut history (events ++ delta) next := by
  have restored := history_restore last
  have combined := observeHistory_splice edge history.dropLast current tail
  rw [restored, observed, localObserved] at combined
  change observeHistory edge (history.dropLast ++ current :: tail) = .ok (events ++ delta) at combined
  refine ⟨frame, ?_, ?_, tail, recorded, cuts⟩
  · rw [recorded, ← restored, List.append_assoc]
    simpa only [List.singleton_append, List.append_nil] using combined
  · rw [recorded, ← restored, List.append_assoc]
    simp only [List.singleton_append, List.getLast?_append, lastNext, Option.some_or]

end SegmentTrace

/-- An executed segment produces an annotation and establishes its proved
invariant/audit. Annotations are proof-side witnesses, not machine state or
an alternative execution semantics. In particular they can index source
states and observations in a simulation relation. -/
def Segment [Labels] {Annotation : Type} (fetch : Int64 → Option Decoded)
    (Audit : List MachineState → Annotation → Executed → Prop)
    (initial : Executed) (post : Annotation → Executed → Prop) : Prop :=
  Eventually (historyStep fetch) (fun final => ∃ a, post a final ∧ Audit initial.history a final) initial

/-- Compose actual execution and its audit together. Every next segment must
execute from the exact returned machine/history. Audit composition is a
proved law of the chosen invariant, not an additional binary premise. -/
theorem Segment.bind [Labels] {Annotation : Type} {fetch : Int64 → Option Decoded}
    {Audit : List MachineState → Annotation → Executed → Prop} {initial : Executed}
    {P Q : Annotation → Executed → Prop}
    (compose : ∀ {h a b s t}, Audit h a s → Audit s.history b t → Audit h b t)
    (first : Segment fetch Audit initial P)
    (next : ∀ s a, P a s → Audit initial.history a s → Segment fetch Audit s Q) :
    Segment fetch Audit initial Q := by
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro s ⟨a, post, audit⟩
  apply eventually_weaken (historyStep fetch) _ _ _ _ (next s a post audit)
  rintro t ⟨b, post, later⟩
  exact ⟨b, post, compose audit later⟩

end Binary
