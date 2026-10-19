import AllowedipsCorrespondence
import ObservationLocations

namespace Binary.AllowedipsCorrespondence
open Leanux LookupObservation

private abbrev observe := AllowedipsObservation.observe
private abbrev edge := AllowedipsObservation.edge

/-- Every emitted point stores the actual edge successor. -/
theorem edge_targets (rxSection : Nat) (before after : MachineState)
    (delta : List Point) (observed : edge rxSection before after = .ok delta) :
    ∀ point ∈ delta, point.machine = after := by
  unfold edge AllowedipsObservation.edge at observed
  dsimp only at observed
  by_cases h0 : before.pc = AllowedipsImage.Lookup.entry+0x41
  · rw [ite_eq_left h0] at observed
    cases selected : choice after.pc (AllowedipsImage.Lookup.entry+0x171) (AllowedipsImage.Lookup.entry+0x47) with
    | error error => rw [selected] at observed; cases observed
    | ok value =>
      rw [selected] at observed
      change Except.ok _ = Except.ok delta at observed
      have equal := Except.ok.inj observed
      subst delta
      cases value <;> simp [decision]
  · rw [ite_eq_right h0] at observed
    by_cases h1 : before.pc = AllowedipsImage.Lookup.entry+0x5b
    · rw [ite_eq_left h1] at observed
      cases selected : choice after.pc (AllowedipsImage.Lookup.entry+0x14f) (AllowedipsImage.Lookup.entry+0x61) with
      | error error => rw [selected] at observed; cases observed
      | ok value =>
        rw [selected] at observed
        change Except.ok _ = Except.ok delta at observed
        have equal := Except.ok.inj observed
        subst delta
        cases value <;> simp [decision]
    · rw [ite_eq_right h1] at observed
      by_cases h2 : before.pc = AllowedipsImage.Lookup.entry+0x81
      · rw [ite_eq_left h2] at observed
        cases selected : choice after.pc (AllowedipsImage.Lookup.entry+0x87) (AllowedipsImage.Lookup.entry+0x184) with
        | error error => rw [selected] at observed; cases observed
        | ok value =>
          rw [selected] at observed
          change Except.ok _ = Except.ok delta at observed
          have equal := Except.ok.inj observed
          subst delta
          cases value <;> simp [decision]
      · rw [ite_eq_right h2] at observed
        by_cases h3 : before.pc = AllowedipsImage.Lookup.entry+0xd3
        · rw [ite_eq_left h3] at observed
          cases selected : choice after.pc (AllowedipsImage.Lookup.entry+0xd5) (AllowedipsImage.Lookup.entry+0x101) with
          | error error => rw [selected] at observed; cases observed
          | ok value =>
            rw [selected] at observed
            change Except.ok _ = Except.ok delta at observed
            have equal := Except.ok.inj observed
            subst delta
            cases value <;> simp [decision]
        · rw [ite_eq_right h3] at observed
          by_cases h4 : before.pc = AllowedipsImage.CommonBits.entry+0x24
          · rw [ite_eq_left h4] at observed
            cases selected : choice after.pc (AllowedipsImage.CommonBits.entry+0x4c) (AllowedipsImage.CommonBits.entry+0x26) with
            | error error => rw [selected] at observed; cases observed
            | ok value =>
              rw [selected] at observed
              change Except.ok _ = Except.ok delta at observed
              have equal := Except.ok.inj observed
              subst delta
              cases value <;> simp [decision]
          · rw [ite_eq_right h4] at observed
            by_cases h5 : before.pc = AllowedipsImage.CommonBits.entry+0x3c
            · rw [ite_eq_left h5] at observed
              cases selected : choice after.pc (AllowedipsImage.CommonBits.entry+0x75) (AllowedipsImage.CommonBits.entry+0x3e) with
              | error error => rw [selected] at observed; cases observed
              | ok value =>
                rw [selected] at observed
                change Except.ok _ = Except.ok delta at observed
                have equal := Except.ok.inj observed
                subst delta
                cases value <;> simp [decision]
            · rw [ite_eq_right h5] at observed
              by_cases h6 : before.pc = AllowedipsImage.CommonBits.entry+0x91
              · rw [ite_eq_left h6] at observed
                cases selected : choice after.pc (AllowedipsImage.CommonBits.entry+0x93) (AllowedipsImage.CommonBits.entry+0xc4) with
                | error error => rw [selected] at observed; cases observed
                | ok value =>
                  rw [selected] at observed
                  change Except.ok _ = Except.ok delta at observed
                  have equal := Except.ok.inj observed
                  subst delta
                  cases value <;> simp [decision]
              · rw [ite_eq_right h6] at observed
                by_cases h7 : before.pc = AllowedipsImage.Lookup.entry+0xff
                · rw [ite_eq_left h7] at observed
                  cases selected : choice after.pc (AllowedipsImage.Lookup.entry+0x90) (AllowedipsImage.Lookup.entry+0x101) with
                  | error error => rw [selected] at observed; cases observed
                  | ok value =>
                    rw [selected] at observed
                    change Except.ok _ = Except.ok delta at observed
                    have equal := Except.ok.inj observed
                    subst delta
                    cases value <;> simp [decision]
                · rw [ite_eq_right h7] at observed
                  by_cases h8 : before.pc = AllowedipsImage.Lookup.entry+0x9b
                  · rw [ite_eq_left h8] at observed
                    cases selected : choice after.pc (AllowedipsImage.Lookup.entry+0x9f) (AllowedipsImage.Lookup.entry+0x9f) with
                    | error error => rw [selected] at observed; cases observed
                    | ok value =>
                      rw [selected] at observed
                      change Except.ok _ = Except.ok delta at observed
                      have equal := Except.ok.inj observed
                      subst delta
                      cases value <;> simp [decision]
                  · rw [ite_eq_right h8] at observed
                    by_cases h9 : before.pc = AllowedipsImage.Lookup.entry+0xb2
                    · rw [ite_eq_left h9] at observed
                      cases selected : choice after.pc (AllowedipsImage.Lookup.entry+0x101) (AllowedipsImage.Lookup.entry+0xb4) with
                      | error error => rw [selected] at observed; cases observed
                      | ok value =>
                        rw [selected] at observed
                        change Except.ok _ = Except.ok delta at observed
                        have equal := Except.ok.inj observed
                        subst delta
                        cases value <;> simp [decision]
                    · rw [ite_eq_right h9] at observed
                      by_cases h10 : before.pc = AllowedipsImage.Lookup.entry+0x109
                      · rw [ite_eq_left h10] at observed
                        cases selected : choice after.pc (AllowedipsImage.Lookup.entry+0x10b) (AllowedipsImage.Lookup.entry+0x184) with
                        | error error => rw [selected] at observed; cases observed
                        | ok value =>
                          rw [selected] at observed
                          change Except.ok _ = Except.ok delta at observed
                          have equal := Except.ok.inj observed
                          subst delta
                          cases value <;> simp [decision]
                      · rw [ite_eq_right h10] at observed
                        by_cases h11 : before.pc = AllowedipsImage.Lookup.entry+0x11c
                        · rw [ite_eq_left h11] at observed
                          cases selected : choice after.pc (AllowedipsImage.Lookup.entry+0x74) (AllowedipsImage.Lookup.entry+0x122) with
                          | error error => rw [selected] at observed; cases observed
                          | ok value =>
                            rw [selected] at observed
                            change Except.ok _ = Except.ok delta at observed
                            have equal := Except.ok.inj observed
                            subst delta
                            cases value <;> simp [decision]
                        · rw [ite_eq_right h11] at observed
                          by_cases h12 : before.pc = AllowedipsImage.Lookup.entry+0xe5
                          · rw [ite_eq_left h12] at observed
                            by_cases wrong : (after.pc != AllowedipsImage.CommonBits.entry) = true
                            · simp only [wrong,ite_true] at observed
                              cases observed
                            · simp only [wrong] at observed
                              change Except.ok _ = Except.ok delta at observed
                              have equal := Except.ok.inj observed
                              subst delta
                              simp [call]
                          · rw [ite_eq_right h12] at observed
                            by_cases h13 : before.pc = AllowedipsImage.CommonBits.entry+0x4b ∨ before.pc = AllowedipsImage.CommonBits.entry+0x74 ∨ before.pc = AllowedipsImage.CommonBits.entry+0xc3
                            · rw [ite_eq_left h13] at observed
                              by_cases wrong : (after.pc != AllowedipsImage.Lookup.entry+0xea) = true
                              · simp only [wrong,ite_true] at observed
                                cases observed
                              · simp only [wrong] at observed
                                change Except.ok _ = Except.ok delta at observed
                                have equal := Except.ok.inj observed
                                subst delta
                                simp [returned]
                            · rw [ite_eq_right h13] at observed
                              by_cases h14 : before.pc = AllowedipsImage.Lookup.entry+0x114
                              · rw [ite_eq_left h14] at observed
                                by_cases wrong : (after.pc != Image.PeerGet.entry) = true
                                · simp only [wrong,ite_true] at observed
                                  cases observed
                                · simp only [wrong] at observed
                                  change Except.ok _ = Except.ok delta at observed
                                  have equal := Except.ok.inj observed
                                  subst delta
                                  simp [call]
                              · rw [ite_eq_right h14] at observed
                                by_cases h15 : before.pc = AllowedipsImage.Lookup.entry+0x14e
                                · rw [ite_eq_left h15] at observed
                                  change Except.ok _ = Except.ok delta at observed
                                  have equal := Except.ok.inj observed
                                  subst delta
                                  simp [returned]
                                · rw [ite_eq_right h15] at observed
                                  by_cases h16 : before.pc = Image.PeerGet.entry+0xaf
                                  · rw [ite_eq_left h16] at observed
                                    by_cases wrong : (after.pc != AllowedipsImage.Lookup.entry+0x119) = true
                                    · simp only [wrong,ite_true] at observed
                                      cases observed
                                    · simp only [wrong] at observed
                                      change Except.ok _ = Except.ok delta at observed
                                      have equal := Except.ok.inj observed
                                      subst delta
                                      simp [returned]
                                  · rw [ite_eq_right h16] at observed
                                    by_cases h17 : (Image.fetchIn Image.PeerGet.entry Image.PeerGet.code before.pc).isSome = true
                                    · rw [ite_eq_left h17] at observed
                                      exact LookupObservation.edge_targets rxSection before after delta observed
                                    · rw [ite_eq_right h17] at observed
                                      change Except.ok [] = Except.ok delta at observed
                                      cases observed
                                      simp

private theorem observe_entry (rxSection : Nat) (initial : MachineState) (rest : List MachineState)
    (entry : initial.pc = AllowedipsImage.Lookup.entry) :
    observe rxSection (initial :: rest) =
      (observeHistory (edge rxSection) (initial :: rest)).map
        (fun records => call "lookup" initial :: records) := by
  simp only [observe, AllowedipsObservation.observe, entry, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem observe_bad_entry (rxSection : Nat) (initial : MachineState) (rest : List MachineState)
    (entry : initial.pc ≠ AllowedipsImage.Lookup.entry) :
    observe rxSection (initial :: rest) = .error "allowedips history does not start at its entry" := by
  have bad : (initial.pc != AllowedipsImage.Lookup.entry) = true := by simp [entry]
  simp only [observe, AllowedipsObservation.observe, bad, ↓reduceIte]
  rfl

theorem observe_extend_raw (rxSection : Nat) (front tail : List MachineState)
    (seen prior delta : List Point)
    (first : observe rxSection front = .ok seen)
    (rawFirst : observeHistory (edge rxSection) front = .ok prior)
    (rawFull : observeHistory (edge rxSection) (front ++ tail) = .ok (prior ++ delta)) :
    observe rxSection (front ++ tail) = .ok (seen ++ delta) := by
  cases front with
  | nil => cases first
  | cons initial rest =>
    by_cases entry : initial.pc = AllowedipsImage.Lookup.entry
    · rw [observe_entry _ _ _ entry, rawFirst] at first
      have equal : seen = call "lookup" initial :: prior :=
        (Except.ok.inj first).symm
      simp only [List.cons_append] at rawFull ⊢
      rw [observe_entry _ _ _ entry, rawFull, equal]
      rfl
    · rw [observe_bad_entry _ _ _ entry] at first
      cases first

theorem observe_prefix (rxSection : Nat) (front rest : List MachineState)
    (all : List Point) (observed : observe rxSection (front ++ rest) = .ok all)
    (nonempty : front ≠ []) :
    ∃ events suffix, observe rxSection front = .ok events ∧ all = events ++ suffix := by
  cases front with
  | nil => exact False.elim (nonempty rfl)
  | cons initial front =>
    by_cases entry : initial.pc = AllowedipsImage.Lookup.entry
    · simp only [List.cons_append] at observed
      rw [observe_entry _ _ _ entry] at observed
      cases raw : observeHistory (edge rxSection) ((initial :: front) ++ rest) with
      | error error =>
        simp only [List.cons_append] at raw
        rw [raw] at observed
        cases observed
      | ok records =>
        have raw' := raw
        simp only [List.cons_append] at raw'
        rw [raw'] at observed
        have equal : all = call "lookup" initial :: records := by
          exact Except.ok.inj observed.symm
        obtain ⟨events, suffix, first, tail⟩ := observeHistory_prefix (edge rxSection)
          (initial :: front) rest records raw
        refine ⟨call "lookup" initial :: events, suffix, ?_, ?_⟩
        · rw [observe_entry _ _ _ entry, first]
          rfl
        · simp only [equal, tail, List.cons_append]
    · simp only [List.cons_append] at observed
      rw [observe_bad_entry _ _ _ entry] at observed
      cases observed

theorem observe_snoc_eq (rxSection : Nat) (history : List MachineState)
    (current next : MachineState) (last : history.getLast? = some current) :
    observe rxSection (history ++ [next]) = (do
      let old ← observe rxSection history
      let delta ← edge rxSection current next
      pure (old ++ delta)) := by
  cases history with
  | nil => cases last
  | cons initial rest =>
    by_cases entry : initial.pc = AllowedipsImage.Lookup.entry
    · have restored := LookupHistory.history_restore last
      have raw := observeHistory_splice (edge rxSection)
        (initial :: rest).dropLast current [next]
      rw [restored] at raw
      have joined : (initial :: rest).dropLast ++ current :: [next] =
          (initial :: rest) ++ [next] := by
        calc
          _ = ((initial :: rest).dropLast ++ [current]) ++ [next] := by simp only [List.append_assoc, List.singleton_append]
          _ = _ := by rw [restored]
      rw [joined] at raw
      simp only [observeHistory, List.cons_append] at raw
      simp only [List.cons_append, observe_entry _ _ _ entry]
      rw [raw]
      cases observeHistory (edge rxSection) (initial :: rest) <;>
        cases edge rxSection current next <;> try rfl
      change Except.ok _ = Except.ok _
      simp only [List.append_nil, List.cons_append]
    · simp only [List.cons_append, observe_bad_entry _ _ _ entry]
      rfl

theorem observe_between (rxSection : Nat) (front middle tail : List MachineState)
    (seen delta : List Point)
    (first : observe rxSection front = .ok seen)
    (full : observe rxSection (front ++ middle ++ tail) = .ok (seen ++ delta)) :
    ∃ localDelta remaining, delta = localDelta ++ remaining ∧
      observe rxSection (front ++ middle) = .ok (seen ++ localDelta) := by
  have nonempty : front ≠ [] := by intro empty; subst front; cases first
  have joinedNonempty : front ++ middle ≠ [] := by
    intro empty
    exact nonempty (List.append_eq_nil_iff.mp empty).1
  obtain ⟨localEvents, remaining, localObs, allEq⟩ :=
    observe_prefix rxSection (front ++ middle) tail (seen ++ delta) full joinedNonempty
  obtain ⟨initialEvents, localDelta, initialObs, localEq⟩ :=
    observe_prefix rxSection front middle localEvents localObs nonempty
  have equal : initialEvents = seen := Except.ok.inj (initialObs.symm.trans first)
  subst initialEvents
  refine ⟨localDelta, remaining, ?_, ?_⟩
  · rw [localEq, List.append_assoc] at allEq
    exact List.append_cancel_left allEq
  · simpa only [localEq] using localObs

private theorem snoc_induction {α : Type} {P : List α → Prop}
    (empty : P []) (snoc : ∀ history next, P history → P (history ++ [next])) :
    ∀ history, P history := by
  intro history
  have reversed : ∀ xs : List α, P xs.reverse := by
    intro xs
    induction xs with
    | nil => exact empty
    | cons next rest ih => simpa using snoc rest.reverse next ih
  simpa using reversed history.reverse

/-- Locate each event at its emitting edge in the supplied raw history.
    Several source decisions may share that edge; none occurs earlier. -/
theorem observe_locate (rxSection : Nat) (history : List MachineState)
    (events : List Point) (observed : observe rxSection history = .ok events)
    (j : Nat) (point : Point) (present : events[j]? = some point) :
    ∃ i localEvents,
      history[i]? = some point.machine ∧
      observe rxSection (history.take (i + 1)) = .ok localEvents ∧
      j + 1 ≤ localEvents.length ∧
      events.take (j + 1) = localEvents.take (j + 1) ∧
      (i = 0 ∨ ∃ earlier, observe rxSection (history.take i) = .ok earlier ∧
        earlier.length ≤ j) := by
  induction history using snoc_induction generalizing events j point with
  | empty => cases observed
  | snoc history next ih =>
    cases oldLast : history.getLast? with
    | none =>
      have empty : history = [] := List.getLast?_eq_none_iff.mp oldLast
      subst history
      by_cases entry : next.pc = AllowedipsImage.Lookup.entry
      · have equal : events = [call "lookup" next] := by
          have h := observed
          simp only [List.nil_append, observe_entry _ _ _ entry, observeHistory] at h
          exact (Except.ok.inj h).symm
        subst events
        have bound := (List.getElem?_eq_some_iff.mp present).1
        have zero : j = 0 := by simp only [List.length_singleton] at bound; omega
        subst j
        have pointEq : point = call "lookup" next := by
          simpa using present.symm
        subst point
        refine ⟨0, [call "lookup" next], ?_, ?_, by simp, rfl, Or.inl rfl⟩
        · rfl
        · simpa using observed
      · rw [List.nil_append, observe_bad_entry _ _ _ entry] at observed
        cases observed
    | some current =>
      have step := observed
      rw [observe_snoc_eq _ _ _ _ oldLast] at step
      cases old : observe rxSection history with
      | error error => rw [old] at step; cases step
      | ok prior =>
        rw [old] at step
        cases emitted : edge rxSection current next with
        | error error => rw [emitted] at step; cases step
        | ok delta =>
          rw [emitted] at step
          have equal : events = prior ++ delta := (Except.ok.inj step).symm
          subst events
          by_cases priorIndex : j < prior.length
          · have oldPresent : prior[j]? = some point := by
              simpa only [List.getElem?_append_left priorIndex] using present
            obtain ⟨i, localEvents, stateAt, localObs, bound, prefixEq, earlier⟩ :=
              ih prior old j point oldPresent
            have hi := (List.getElem?_eq_some_iff.mp stateAt).1
            have takeNext : (history ++ [next]).take (i + 1) = history.take (i + 1) :=
              List.take_append_of_le_length (by omega)
            have takePrior : (history ++ [next]).take i = history.take i :=
              List.take_append_of_le_length (by omega)
            refine ⟨i, localEvents, ?_, ?_, bound, ?_, ?_⟩
            · simpa only [List.getElem?_append_left hi] using stateAt
            · simpa only [takeNext] using localObs
            · rw [List.take_append_of_le_length (by omega)]
              exact prefixEq
            · simpa only [takePrior] using earlier
          · have newPresent : delta[j - prior.length]? = some point := by
              simpa only [List.getElem?_append_right (by omega : prior.length ≤ j)] using present
            have target := edge_targets rxSection current next delta emitted point
              (List.mem_of_getElem? newPresent)
            have bound := (List.getElem?_eq_some_iff.mp present).1
            refine ⟨history.length, prior ++ delta, ?_, ?_, by omega, rfl, Or.inr ⟨prior, ?_, by omega⟩⟩
            · simp [target]
            · rw [List.take_of_length_le (by simp)]
              exact observed
            · simpa using old


end Binary.AllowedipsCorrespondence
