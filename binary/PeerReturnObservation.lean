import CorrespondencePrefix
import PeerPhaseSchedule

namespace Binary.LookupObservation
open Leanux

theorem edge_helper_return_pc (rxSection : Nat) (before after : MachineState)
    (delta : List Point) (observed : edge rxSection before after = .ok delta) :
    ∀ point ∈ delta, point.tag = .returned "wg_peer_get_maybe_zero" →
      before.pc = Image.PeerGet.entry+0xaf := by
  unfold edge at observed
  dsimp only at observed
  by_cases h0 : before.pc = Image.Lookup.entry + 0x32 ∨ before.pc = Image.Lookup.entry + 0x6a
  · rw [ite_eq_left h0] at observed
    cases selected : choice after.pc (Image.Lookup.entry + 0x34) (Image.Lookup.entry + 0x6c) with
    | error error =>
      rw [selected] at observed
      cases observed
    | ok value =>
      rw [selected] at observed
      change Except.ok _ = Except.ok delta at observed
      have equal := Except.ok.inj observed
      subst delta
      cases value <;> simp [decision]
  · rw [ite_eq_right h0] at observed
    by_cases h1 : before.pc = Image.Lookup.entry + 0x5c
    · rw [ite_eq_left h1] at observed
      cases selected : choice after.pc (Image.Lookup.entry + 0x95) (Image.Lookup.entry + 0x5e) with
      | error error =>
        rw [selected] at observed
        cases observed
      | ok value =>
        rw [selected] at observed
        change Except.ok _ = Except.ok delta at observed
        have equal := Except.ok.inj observed
        subst delta
        cases value <;> simp [decision]
    · rw [ite_eq_right h1] at observed
      by_cases h2 : before.pc = Image.Lookup.entry + 0xab
      · rw [ite_eq_left h2] at observed
        cases selected : choice after.pc (Image.Lookup.entry + 0xad) (Image.Lookup.entry + 0x71) with
        | error error =>
          rw [selected] at observed
          cases observed
        | ok value =>
          rw [selected] at observed
          change Except.ok _ = Except.ok delta at observed
          have equal := Except.ok.inj observed
          subst delta
          cases value <;> simp [decision]
      · rw [ite_eq_right h2] at observed
        by_cases h3 : before.pc = Image.Lookup.entry + 0xb5
        · rw [ite_eq_left h3] at observed
          by_cases wrong : (after.pc != Image.PeerGet.entry) = true
          · simp only [wrong, ite_true] at observed
            cases observed
          · simp only [wrong] at observed
            change Except.ok _ = Except.ok delta at observed
            have equal := Except.ok.inj observed
            subst delta
            simp [call]
        · rw [ite_eq_right h3] at observed
          by_cases h4 : before.pc = Image.Lookup.entry + 0xc3
          · rw [ite_eq_left h4] at observed
            cases selected : choice after.pc (Image.Lookup.entry + 0xc5) (Image.Lookup.entry + 0x71) with
            | error error =>
              rw [selected] at observed
              cases observed
            | ok value =>
              rw [selected] at observed
              change Except.ok _ = Except.ok delta at observed
              have equal := Except.ok.inj observed
              subst delta
              cases value <;> simp [decision]
          · rw [ite_eq_right h4] at observed
            by_cases h5 : before.pc = Image.Lookup.entry + 0x94
            · rw [ite_eq_left h5] at observed
              change Except.ok _ = Except.ok delta at observed
              have equal := Except.ok.inj observed
              subst delta
              simp [returned]
            · rw [ite_eq_right h5] at observed
              by_cases h6 : before.pc = Image.PeerGet.entry + 0x15
              · rw [ite_eq_left h6] at observed
                cases selected : choice after.pc (Image.PeerGet.entry + 0xdd) (Image.PeerGet.entry + 0x1b) with
                | error error =>
                  rw [selected] at observed
                  cases observed
                | ok value =>
                  rw [selected] at observed
                  change Except.ok _ = Except.ok delta at observed
                  have equal := Except.ok.inj observed
                  subst delta
                  cases value <;> simp [decision]
              · rw [ite_eq_right h6] at observed
                by_cases h7 : before.pc = Image.PeerGet.entry + 0x3d
                · rw [ite_eq_left h7] at observed
                  cases selected : choice after.pc (Image.PeerGet.entry + 0xb0) (Image.PeerGet.entry + 0x3f) with
                  | error error =>
                    rw [selected] at observed
                    cases observed
                  | ok value =>
                    rw [selected] at observed
                    change Except.ok _ = Except.ok delta at observed
                    have equal := Except.ok.inj observed
                    subst delta
                    cases value <;> simp [decision]
                · rw [ite_eq_right h7] at observed
                  by_cases h8 : before.pc = Image.PeerGet.entry + 0x63
                  · rw [ite_eq_left h8] at observed
                    cases selected : choice after.pc (Image.PeerGet.entry + 0xf2) (Image.PeerGet.entry + 0x69) with
                    | error error =>
                      rw [selected] at observed
                      cases observed
                    | ok value =>
                      rw [selected] at observed
                      change Except.ok _ = Except.ok delta at observed
                      have equal := Except.ok.inj observed
                      subst delta
                      cases value <;> simp [decision]
                  · rw [ite_eq_right h8] at observed
                    by_cases h9 : before.pc = Image.PeerGet.entry + 0x79
                    · rw [ite_eq_left h9] at observed
                      cases selected : choice after.pc (Image.PeerGet.entry + 0xe1) (Image.PeerGet.entry + 0x7b) with
                      | error error =>
                        rw [selected] at observed
                        cases observed
                      | ok value =>
                        rw [selected] at observed
                        change Except.ok _ = Except.ok delta at observed
                        have equal := Except.ok.inj observed
                        subst delta
                        cases value <;> simp [decision]
                    · rw [ite_eq_right h9] at observed
                      by_cases h10 : before.pc = Image.PeerGet.entry + 0x8d
                      · rw [ite_eq_left h10] at observed
                        cases selected : choice after.pc (Image.PeerGet.entry + 0xe1) (Image.PeerGet.entry + 0x8f) with
                        | error error =>
                          rw [selected] at observed
                          cases observed
                        | ok value =>
                          rw [selected] at observed
                          change Except.ok _ = Except.ok delta at observed
                          have equal := Except.ok.inj observed
                          subst delta
                          cases value <;> simp [decision]
                      · rw [ite_eq_right h10] at observed
                        by_cases h11 : before.pc = Image.PeerGet.entry + 0x94
                        · rw [ite_eq_left h11] at observed
                          change Except.ok _ = Except.ok delta at observed
                          have equal := Except.ok.inj observed
                          subst delta
                          simp [decision]
                        · rw [ite_eq_right h11] at observed
                          by_cases h12 : before.pc = Image.PeerGet.entry + 0xb5
                          · rw [ite_eq_left h12] at observed
                            change Except.ok _ = Except.ok delta at observed
                            have equal := Except.ok.inj observed
                            subst delta
                            simp [decision]
                          · rw [ite_eq_right h12] at observed
                            by_cases h13 : before.pc = Image.PeerGet.entry + 0xc3
                            · rw [ite_eq_left h13] at observed
                              change Except.ok _ = Except.ok delta at observed
                              have equal := Except.ok.inj observed
                              subst delta
                              simp [decision]
                            · rw [ite_eq_right h13] at observed
                              by_cases h14 : before.pc = Image.PeerGet.entry + 0xd4
                              · rw [ite_eq_left h14] at observed
                                change Except.ok _ = Except.ok delta at observed
                                have equal := Except.ok.inj observed
                                subst delta
                                simp [decision]
                              · rw [ite_eq_right h14] at observed
                                by_cases h15 : before.pc = Image.PeerGet.entry + 0xaf
                                · rw [ite_eq_left h15] at observed
                                  change Except.ok _ = Except.ok delta at observed
                                  have equal := Except.ok.inj observed
                                  subst delta
                                  simp [returned, h15]
                                · rw [ite_eq_right h15] at observed
                                  change Except.ok [] = Except.ok delta at observed
                                  have equal := Except.ok.inj observed
                                  subst delta
                                  simp


/-- If the actual scanner stays nonempty at every prefix, no helper RET
    has been observed. The seed is only a proof device; no source operand
    or extra machine state is supplied to the observer. -/
theorem no_helper_return_of_scan_nonempty (rx : Nat) (history : List MachineState)
    (events : List Point) (seed : Option PeerCountPhase.Pending)
    (observed : observeHistory (edge rx) history = .ok events)
    (nonempty : ∀ n, PeerCountPhase.scan seed (history.take n) ≠ none) :
    ∀ point ∈ events, point.tag ≠ .returned "wg_peer_get_maybe_zero" := by
  induction history generalizing events seed with
  | nil => cases observed; simp
  | cons before rest ih =>
    cases rest with
    | nil => cases observed; simp
    | cons after rest =>
      simp only [observeHistory] at observed
      cases emitted : edge rx before after with
      | error error => rw [emitted] at observed; cases observed
      | ok delta =>
        rw [emitted] at observed
        cases tail : observeHistory (edge rx) (after :: rest) with
        | error error => rw [tail] at observed; cases observed
        | ok remaining =>
          rw [tail] at observed
          have equal : events = delta ++ remaining := (Except.ok.inj observed).symm
          subst events
          have firstNonempty : PeerCountPhase.edge seed before after ≠ none := by
            simpa only [List.take_succ_cons, List.take_zero, PeerCountPhase.scan] using nonempty 2
          have later : ∀ n, PeerCountPhase.scan (PeerCountPhase.edge seed before after)
              ((after :: rest).take n) ≠ none := by
            intro n
            cases n with
            | zero => exact firstNonempty
            | succ n =>
              simpa only [List.take_succ_cons, PeerCountPhase.scan] using nonempty (n+2)
          intro point member tag
          rcases List.mem_append.mp member with first | last
          · have pc := edge_helper_return_pc rx before after delta emitted point first tag
            exact firstNonempty (by simp only [PeerCountPhase.edge, pc, ite_true])
          · exact ih remaining (PeerCountPhase.edge seed before after) tail later point last tag

theorem observe_no_helper_return_of_scan_nonempty (rx : Nat) (history : List MachineState)
    (events : List Point) (seed : PeerCountPhase.Pending)
    (observed : observe rx history = .ok events)
    (nonempty : ∀ n, PeerCountPhase.scan (some seed) (history.take n) ≠ none) :
    ∀ point ∈ events, point.tag ≠ .returned "wg_peer_get_maybe_zero" := by
  cases history with
  | nil => cases observed
  | cons initial rest =>
    unfold observe at observed
    dsimp only at observed
    split at observed
    · cases observed
    · cases raw : observeHistory (edge rx) (initial :: rest) with
      | error error => rw [raw] at observed; cases observed
      | ok delta =>
        rw [raw] at observed
        have recorded : events = call "wg_index_hashtable_lookup" initial :: delta :=
          (Except.ok.inj observed).symm
        rw [recorded]
        intro point member
        rcases List.mem_cons.mp member with equal | later
        · subst point; simp [call]
        · exact no_helper_return_of_scan_nonempty rx (initial :: rest) delta (some seed)
            raw nonempty point later

/-- A reset only on the final raw edge identifies the executed RET.
    This is used to locate the decision-only prefix before the returned
    marker, without selecting an arbitrary occurrence of a repeated state. -/
theorem helper_return_prefix (rx : Nat) (history : List MachineState)
    (current : MachineState) (events : List Point) (seed : PeerCountPhase.Pending)
    (last : history.getLast? = some current)
    (proper : ∀ n, n < history.length →
      PeerCountPhase.scan (some seed) (history.take n) ≠ none)
    (cleared : PeerCountPhase.scan (some seed) history = none)
    (observed : observe rx history = .ok (events ++ [returned "wg_peer_get_maybe_zero" current])) :
    observe rx history.dropLast = .ok events := by
  have restored := LookupHistory.history_restore last
  cases previous : history.dropLast.getLast? with
  | none =>
    have empty : history.dropLast = [] := List.getLast?_eq_none_iff.mp previous
    rw [← restored, empty] at cleared
    cases cleared
  | some before =>
    have earlier : PeerCountPhase.scan (some seed) history.dropLast ≠ none := by
      rw [List.dropLast_eq_take]
      apply proper
      have nonempty : history ≠ [] := by intro empty; rw [empty] at last; cases last
      have positive := List.length_pos_iff.mpr nonempty
      omega
    have edgeReset := PeerCountPhase.scan_snoc (some seed) history.dropLast before current previous
    rw [restored, cleared] at edgeReset
    have pc : before.pc = Image.PeerGet.entry+0xaf := by
      unfold PeerCountPhase.edge at edgeReset
      split at edgeReset
      · assumption
      · split at edgeReset
        · cases edgeReset
        · exact False.elim (earlier edgeReset.symm)
    have emitted : edge rx before current = .ok [returned "wg_peer_get_maybe_zero" current] := by
      simp [edge, pc, Image.Lookup.entry, Image.PeerGet.entry]
      rfl
    have all := observe_snoc_eq rx history.dropLast before current previous
    rw [restored, emitted, observed] at all
    cases first : observe rx history.dropLast with
    | error error => rw [first] at all; cases all
    | ok prefixEvents =>
      rw [first] at all
      have equal : events ++ [returned "wg_peer_get_maybe_zero" current] =
          prefixEvents ++ [returned "wg_peer_get_maybe_zero" current] := Except.ok.inj all
      exact congrArg Except.ok (List.append_cancel_right equal).symm

#print axioms helper_return_prefix
#print axioms observe_no_helper_return_of_scan_nonempty
#print axioms no_helper_return_of_scan_nonempty
#print axioms edge_helper_return_pc
end Binary.LookupObservation
