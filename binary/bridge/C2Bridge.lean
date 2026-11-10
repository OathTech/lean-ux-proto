import C2Headline
import Leanux.Proofs.WG.CounterWindow.Model
import Leanux.Proofs.WG.CounterWindow.Refinement
import Leanux.Proofs.WG.CounterWindow.MirrorCalls
import Leanux.Proofs.WG.CounterWindow.Bounds

/-! Result C2, the bridge: the transported clause.

The one library that imports both the binary package and the proof tree, and of the
proof tree exactly the four `CounterWindow` modules above. It joins the refinement
proved in the binary package (`Refines`: the range computes the mirror's
`counterValidate`) with two landed theorems:

* `CounterWindow.mirror_step` (the S2 refinement): `counterValidate` on a world holding
  a 128-word window `c` succeeds, returns `(step c nonce).1` and leaves `(step c nonce).2`;
* `CounterWindow.accepted_nodup` (R1's `pure_uniqueness`): the counters `step` accepts in
  sequence are distinct.

`accepts_as_pure_window` and `no_counter_accepted_twice_of_parts` take the refinement
and the representation as hypotheses; `no_counter_accepted_twice` and `headline` are
closed, on the binary package's `refines`, `representation`, `exits_cleanly` and
`replay_witness` (`C2Headline`). `headline` is the track's headline theorem. -/
namespace Binary.C2.Bridge
open Binary TrustBase Leanux Binary.C2
open Leanux.Proofs.WG
local instance : Labels := Binary.Image.linkedLabels

/-- THE JOIN. Over any visits of one retained window whose first entry represents `c`,
the machine accepts exactly the packet counters the pure window accepts from `c`. -/
def AcceptsAsPureWindow : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (kp : BitVec 64) (visits : List Visit)
    (c : WG.ReplayCounter),
    Reading fetch → Visits fetch kp visits →
    (∀ first, visits.head? = some first →
      Layouts.ReplayFields first.entry.data.dmem (windowBase kp) c) →
    (acceptedNonces visits).map (·.toNat) =
      CounterWindow.accepted c (visits.map (·.nonce.toNat))

theorem accepts_as_pure_window (refines : Refines) (representation : Representation) :
    AcceptsAsPureWindow := by
  intro fetch kp visits
  induction visits with
  | nil =>
    intro c _ _ _
    simp [acceptedNonces, CounterWindow.accepted]
  | cons v rest ih =>
    intro c reading visits fields
    have fields₀ := fields v rfl
    obtain ⟨layout, preempt, skb, context⟩ := visits.entries v (by simp)
    obtain ⟨world, id, ambient, held⟩ := representation.world c
    obtain ⟨world', ambient', run, held'⟩ :=
      CounterWindow.mirror_step world ambient id c v.nonce.toNat held fields₀.2.1
    have simulation := refines fetch layout preempt v.entry kp skb v.nonce world world'
      ambient ambient' id c _ reading context fields₀ held run
    have atExit : Eventually (historyStep fetch)
        (fun e => e.machine.pc ∈ exits ∧ (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧
          (accepted e.machine = (CounterWindow.step c v.nonce.toNat).1 ∧
            ∃ c', windowOf world' id = some c' ∧
              Layouts.ReplayFields e.machine.data.dmem (windowBase kp) c'))
        ⟨v.entry, [v.entry]⟩ := by
      apply eventually_weaken (historyStep fetch) _ _ _ _ simulation
      rintro e ⟨pc, early, result, window, _⟩
      exact ⟨pc ▸ exitPC_mem c v.nonce.toNat, early, result, window⟩
    obtain ⟨result, c', heldExit, fieldsExit⟩ := representation.determined fetch v.entry v.exit
      (fun t => accepted t = (CounterWindow.step c v.nonce.toNat).1 ∧
        ∃ c', windowOf world' id = some c' ∧
          Layouts.ReplayFields t.data.dmem (windowBase kp) c')
      atExit (visits.exits v (by simp))
    have same : c' = (CounterWindow.step c v.nonce.toNat).2 :=
      Option.some.inj (heldExit.symm.trans held')
    subst same
    have restVisits : Visits fetch kp rest := by
      refine ⟨fun u member => visits.entries u (by simp [member]),
        fun u member => visits.exits u (by simp [member]), ?_⟩
      cases rest with
      | nil => trivial
      | cons second more => exact visits.retained.2
    have tail := ih (CounterWindow.step c v.nonce.toNat).2 reading restVisits (by
      intro first isFirst
      cases rest with
      | nil => simp at isFirst
      | cons second more =>
        simp only [List.head?_cons, Option.some.injEq] at isFirst
        subst isFirst
        exact representation.retained _ _ kp _ fieldsExit visits.retained.1)
    unfold acceptedNonces at tail ⊢
    simp only [List.filter_cons, List.map_cons, CounterWindow.accepted, result]
    cases (CounterWindow.step c v.nonce.toNat).1 <;> simpa using tail

/-- CLAUSE `NoCounterAcceptedTwice`: the landed uniqueness theorem, transported to the
machine code through the refinement. -/
theorem no_counter_accepted_twice_of_parts (refines : Refines)
    (representation : Representation) : NoCounterAcceptedTwice := by
  intro fetch kp visits reading held
  have start : ∃ c : WG.ReplayCounter, c.backtrack.size = 128 ∧
      ∀ first, visits.head? = some first →
        Layouts.ReplayFields first.entry.data.dmem (windowBase kp) c := by
    cases visits with
    | nil => exact ⟨{}, by simp, by simp⟩
    | cons v rest =>
      obtain ⟨layout, preempt, skb, context⟩ := held.entries v (by simp)
      obtain ⟨w, window⟩ := representation.mapped v.entry.data.dmem kp context.window
      have fields := representation.toFields _ _ _ window
      refine ⟨toCounter w, fields.2.1, ?_⟩
      intro first isFirst
      simp only [List.head?_cons, Option.some.injEq] at isFirst
      subst isFirst
      exact fields
  obtain ⟨c, size, fields⟩ := start
  have joined := accepts_as_pure_window refines representation fetch kp visits c reading held fields
  have distinct := CounterWindow.accepted_nodup c (visits.map (·.nonce.toNat)) size
  rw [← joined] at distinct
  exact List.Pairwise.of_map (·.toNat) (fun a b differ equal => differ (equal ▸ rfl)) distinct

/-- CLAUSE `NoCounterAcceptedTwice`, closed. -/
theorem no_counter_accepted_twice : NoCounterAcceptedTwice :=
  no_counter_accepted_twice_of_parts refines representation

/-- THE HEADLINE of result C2, closed. -/
theorem headline : HeadlineRefinement :=
  ⟨exits_cleanly, refines, no_counter_accepted_twice, replay_witness⟩

/-- The exclusion `ReplayRefused`, in no headline: a corollary of the transported
clause. A packet counter that an earlier visit accepted is refused by the range. -/
theorem replay_refused : ReplayRefused := by
  intro fetch kp before between earlier later reading visits same acceptedEarlier
  have distinct := no_counter_accepted_twice fetch kp _ reading visits
  cases acceptedLater : accepted later.exit with
  | false => rfl
  | true =>
    exfalso
    unfold acceptedNonces at distinct
    simp [List.filter_append, acceptedEarlier, acceptedLater, same, List.nodup_append,
      List.nodup_cons] at distinct

#print axioms accepts_as_pure_window
#print axioms no_counter_accepted_twice_of_parts
#print axioms no_counter_accepted_twice
#print axioms headline
#print axioms replay_refused
end Binary.C2.Bridge
