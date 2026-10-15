import KcovExecution
import LookupObservation

namespace Binary.LookupObservation
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Every edge that can emit an anchored observation starts at an actual
    instruction in the pinned anchor image. Service interiors therefore
    cannot emit these observations under the named no-reentry contract. -/
theorem edge_unanchored (rxSection : Nat) (s t : MachineState)
    (unanchored : Image.fetch s.pc = none) : edge rxSection s t = .ok [] := by
  have avoid (pc : Int64) (mapped : (Image.fetch pc).isSome = true) : s.pc ≠ pc := by
    intro eq
    rw [← eq, unanchored] at mapped
    cases mapped
  have hLookup32 := avoid (Image.Lookup.entry+0x32) (by decide)
  have hLookup6a := avoid (Image.Lookup.entry+0x6a) (by decide)
  have hLookup5c := avoid (Image.Lookup.entry+0x5c) (by decide)
  have hLookupab := avoid (Image.Lookup.entry+0xab) (by decide)
  have hLookupb5 := avoid (Image.Lookup.entry+0xb5) (by decide)
  have hLookupc3 := avoid (Image.Lookup.entry+0xc3) (by decide)
  have hLookup94 := avoid (Image.Lookup.entry+0x94) (by decide)
  have hPeerGet15 := avoid (Image.PeerGet.entry+0x15) (by decide)
  have hPeerGet3d := avoid (Image.PeerGet.entry+0x3d) (by decide)
  have hPeerGet63 := avoid (Image.PeerGet.entry+0x63) (by decide)
  have hPeerGet79 := avoid (Image.PeerGet.entry+0x79) (by decide)
  have hPeerGet8d := avoid (Image.PeerGet.entry+0x8d) (by decide)
  have hPeerGet94 := avoid (Image.PeerGet.entry+0x94) (by decide)
  have hPeerGetb5 := avoid (Image.PeerGet.entry+0xb5) (by decide)
  have hPeerGetc3 := avoid (Image.PeerGet.entry+0xc3) (by decide)
  have hPeerGetd4 := avoid (Image.PeerGet.entry+0xd4) (by decide)
  have hPeerGetaf := avoid (Image.PeerGet.entry+0xaf) (by decide)
  simp only [edge, hLookup32, hLookup6a, hLookup5c, hLookupab, hLookupb5, hLookupc3, hLookup94, hPeerGet15, hPeerGet3d, hPeerGet63, hPeerGet79, hPeerGet8d, hPeerGet94, hPeerGetb5, hPeerGetc3, hPeerGetd4, hPeerGetaf, false_or, ite_false]
  rfl

theorem no_reentry_observations (rxSection : Nat) (history : List MachineState)
    (noReentry : NoAnchoredReentry history) :
    observeHistory (edge rxSection) history = .ok [] := by
  induction history with
  | nil => rfl
  | cons s rest ih =>
    cases rest with
    | nil => rfl
    | cons t rest =>
      have current : Image.fetch s.pc = none := noReentry s (by simp)
      have tail : NoAnchoredReentry (t :: rest) := by
        intro q present
        exact noReentry q (by simp only [List.dropLast_cons_cons, List.mem_cons]; exact .inr present)
      change (do
        let here ← edge rxSection s t
        let later ← observeHistory (edge rxSection) (t :: rest)
        pure (here ++ later)) = .ok []
      rw [edge_unanchored rxSection s t current, ih tail]
      rfl

/-- All declared stuttering cuts are actual anchored instruction addresses. -/
theorem cut_is_anchored (pc : Int64) (cut : pc ∈ Image.cutPoints) :
    (Image.fetch pc).isSome = true := by
  have checked : Image.cutPoints.all (fun pc => (Image.fetch pc).isSome) = true := by decide
  exact List.all_eq_true.mp checked pc cut

theorem no_reentry_cuts (history : List MachineState) (noReentry : NoAnchoredReentry history)
    (s : MachineState) (present : s ∈ history.dropLast) : s.pc ∉ Image.cutPoints := by
  intro cut
  have mapped := cut_is_anchored s.pc cut
  rw [noReentry s present] at mapped
  cases mapped

/-- Instruction execution retains every supplied incoming state. This
    invariant derives the local service's initial state in its final history. -/
theorem history_prefix (fetch : Int64 → Option Decoded) (Q : Executed → Prop)
    (s : Executed) (front : List MachineState) (initialPrefix : front <+: s.history)
    (run : Eventually (historyStep fetch) Q s) :
    Eventually (historyStep fetch) (fun t => Q t ∧ front <+: t.history) s := by
  induction run with
  | done s h => exact .done s ⟨h, initialPrefix⟩
  | step s mid hs rest ih =>
    apply step_cps
    apply instruction_mono fetch s.machine _ _ _ hs
    intro t ht
    exact ih ⟨t, s.history ++ [t]⟩ ht (initialPrefix.trans ⟨[t], rfl⟩)

/-- Insert a proved service execution into an actual incoming history.
    It changes no anchored observations. Its return state is retained and
    may itself be an anchored cut, whose R obligation belongs to the caller. -/
theorem silent_service (fetch : Int64 → Option Decoded) (rxSection : Nat)
    (Q : Executed → Prop) (s : MachineState)
    (localRun : Eventually (historyStep fetch)
      (fun t => Q t ∧ NoAnchoredReentry t.history) ⟨s, [s]⟩)
    (front : List MachineState) (events : List Point)
    (observed : observeHistory (edge rxSection) (front ++ [s]) = .ok events) :
    Eventually (historyStep fetch)
      (fun t => ∃ localState tail, Q localState ∧
        t.machine = localState.machine ∧ localState.history = s :: tail ∧
        t.history = front ++ s :: tail ∧
        observeHistory (edge rxSection) t.history = .ok events ∧
        NoAnchoredReentry localState.history)
      ⟨s, front ++ [s]⟩ := by
  have prefixed := history_prefix fetch _ ⟨s, [s]⟩ [s] ⟨[], rfl⟩ localRun
  have joined := history_prepend fetch _ _ prefixed front
  apply eventually_weaken (historyStep fetch) _ _ _ _ joined
  rintro t ⟨localState, ⟨⟨good, noReentry⟩, tail, initialPrefix⟩, machine, history⟩
  have localHistory : localState.history = s :: tail := initialPrefix.symm
  refine ⟨localState, tail, good, machine, localHistory, ?_, ?_, noReentry⟩
  · simpa only [localHistory] using history
  · rw [history, localHistory, observeHistory_splice, observed]
    have empty := no_reentry_observations rxSection localState.history noReentry
    rw [localHistory] at empty
    rw [empty]
    exact congrArg Except.ok (List.append_nil events)

/-- Adding actual states outside the anchored cut set creates no new
    correspondence obligation and cannot change an earlier observation. -/
theorem CutsAligned.append_no_cuts {R rxSection history source}
    (aligned : CutsAligned R rxSection history source) (tail : List MachineState)
    (noCuts : ∀ s ∈ tail, s.pc ∉ Image.cutPoints) :
    CutsAligned R rxSection (history ++ tail) source := by
  induction tail generalizing history with
  | nil => simpa only [List.append_nil] using aligned
  | cons s tail ih =>
    have next := aligned.snoc s (fun cut => False.elim (noCuts s (by simp) cut))
    simpa only [List.append_assoc, List.singleton_append] using
      ih next (fun t present => noCuts t (by simp [present]))

theorem CutsAligned.prefix {R rxSection front tail source}
    (aligned : CutsAligned R rxSection (front ++ tail) source) :
    CutsAligned R rxSection front source := by
  intro i current present cut
  have bound := (List.getElem?_eq_some_iff.mp present).1
  have extended : (front ++ tail)[i]? = some current := by
    simpa only [List.getElem?_append_left bound] using present
  obtain ⟨events, last, observed, matched, latest, related⟩ := aligned i current extended cut
  refine ⟨events, last, ?_, matched, latest, related⟩
  simpa [List.take_append, Nat.sub_eq_zero_of_le (show i+1 ≤ front.length by omega)] using observed

/-- Service interiors add no cuts. The caller proves R at the actual return
    state; all earlier cuts and their exact observation prefixes are retained. -/
theorem CutsAligned.service_extension {R rxSection source}
    (front localHistory : List MachineState) (current final : MachineState)
    (aligned : CutsAligned R rxSection (front ++ [current]) source)
    (last : localHistory.getLast? = some final)
    (noCuts : ∀ s ∈ localHistory.dropLast, s.pc ∉ Image.cutPoints)
    (newCut : final.pc ∈ Image.cutPoints →
      ∃ events latest,
        observe rxSection (front ++ localHistory) = .ok events ∧
        PrefixMatches R events source ∧
        (source.take events.length).getLast? = some latest ∧ R events final latest.world) :
    CutsAligned R rxSection (front ++ localHistory) source := by
  have nonempty : localHistory ≠ [] := by intro empty; rw [empty] at last; cases last
  have lastEq : localHistory.getLast nonempty = final := by
    simpa only [List.getLast?_eq_getLast nonempty, Option.some.injEq] using last
  have restored : localHistory.dropLast ++ [final] = localHistory := by
    rw [← lastEq]
    exact List.dropLast_concat_getLast nonempty
  have interior := aligned.prefix.append_no_cuts localHistory.dropLast noCuts
  have extended := interior.snoc final (by
    intro cut
    simpa only [List.append_assoc, restored] using newCut cut)
  simpa only [List.append_assoc, restored] using extended

#print axioms edge_unanchored
#print axioms no_reentry_observations
#print axioms cut_is_anchored
#print axioms no_reentry_cuts
#print axioms history_prefix
#print axioms silent_service
#print axioms CutsAligned.append_no_cuts
#print axioms CutsAligned.prefix
#print axioms CutsAligned.service_extension
end Binary.LookupObservation
