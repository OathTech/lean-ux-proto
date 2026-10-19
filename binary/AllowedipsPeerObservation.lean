import AllowedipsObservation
import ServiceObservation
namespace Binary.AllowedipsPeerObservation
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels
/-- The helper ABI postcondition checks its saved return address. -/
def edge (rxSection : Nat) (s t : MachineState) : Except String (List Point) :=
  if Image.PeerGet.entry ≤ s.pc ∧ s.pc < Image.PeerGet.entry + 0xe4 then
    LookupObservation.edge rxSection s t
  else AllowedipsObservation.edge rxSection s t

theorem edge_unanchored (rxSection : Nat) (s t : MachineState)
    (old : Image.fetch s.pc = none) (new : AllowedipsImage.fetch s.pc = none) :
    edge rxSection s t = .ok [] := by
  have avoid (pc : Int64) (mapped : (AllowedipsImage.fetch pc).isSome = true) : s.pc ≠ pc := by
    intro eq
    rw [← eq, new] at mapped
    cases mapped
  have hLookup41 := avoid (AllowedipsImage.Lookup.entry+0x41) (by decide)
  have hLookup5b := avoid (AllowedipsImage.Lookup.entry+0x5b) (by decide)
  have hLookup81 := avoid (AllowedipsImage.Lookup.entry+0x81) (by decide)
  have hLookupd3 := avoid (AllowedipsImage.Lookup.entry+0xd3) (by decide)
  have hLookupff := avoid (AllowedipsImage.Lookup.entry+0xff) (by decide)
  have hLookup9b := avoid (AllowedipsImage.Lookup.entry+0x9b) (by decide)
  have hLookupb2 := avoid (AllowedipsImage.Lookup.entry+0xb2) (by decide)
  have hLookup109 := avoid (AllowedipsImage.Lookup.entry+0x109) (by decide)
  have hLookup11c := avoid (AllowedipsImage.Lookup.entry+0x11c) (by decide)
  have hLookupe5 := avoid (AllowedipsImage.Lookup.entry+0xe5) (by decide)
  have hLookup114 := avoid (AllowedipsImage.Lookup.entry+0x114) (by decide)
  have hLookup14e := avoid (AllowedipsImage.Lookup.entry+0x14e) (by decide)
  have hCommonBits24 := avoid (AllowedipsImage.CommonBits.entry+0x24) (by decide)
  have hCommonBits3c := avoid (AllowedipsImage.CommonBits.entry+0x3c) (by decide)
  have hCommonBits91 := avoid (AllowedipsImage.CommonBits.entry+0x91) (by decide)
  have hCommonBits4b := avoid (AllowedipsImage.CommonBits.entry+0x4b) (by decide)
  have hCommonBits74 := avoid (AllowedipsImage.CommonBits.entry+0x74) (by decide)
  have hCommonBitsc3 := avoid (AllowedipsImage.CommonBits.entry+0xc3) (by decide)
  have ret : s.pc ≠ Image.PeerGet.entry+0xaf := by
    intro eq
    have h : (Image.fetch (Image.PeerGet.entry+0xaf)).isSome = true := by decide
    rw [← eq, old] at h
    cases h
  have silent := LookupObservation.edge_unanchored rxSection s t old
  simp only [edge]
  split
  · exact silent
  · simp only [AllowedipsObservation.edge, hLookup41, hLookup5b, hLookup81, hLookupd3, hLookupff, hLookup9b, hLookupb2, hLookup109, hLookup11c, hLookupe5, hLookup114, hLookup14e, hCommonBits24, hCommonBits3c, hCommonBits91, hCommonBits4b, hCommonBits74, hCommonBitsc3, ret, false_or, ite_false]
    split <;> first | exact silent | rfl

theorem no_reentry_observations (rxSection : Nat) (history : List MachineState)
    (old : NoAnchoredReentry history) (new : NoAllowedipsReentry history) :
    observeHistory (edge rxSection) history = .ok [] := by
  induction history with
  | nil => rfl
  | cons s rest ih =>
    cases rest with
    | nil => rfl
    | cons t rest =>
      have oldTail : NoAnchoredReentry (t :: rest) := by
        intro q present
        exact old q (by simp only [List.dropLast_cons_cons, List.mem_cons]; exact .inr present)
      have newTail : NoAllowedipsReentry (t :: rest) := by
        intro q present
        exact new q (by simp only [List.dropLast_cons_cons, List.mem_cons]; exact .inr present)
      change (do
        let here ← edge rxSection s t
        let later ← observeHistory (edge rxSection) (t :: rest)
        pure (here ++ later)) = .ok []
      rw [edge_unanchored rxSection s t (old s (by simp)) (new s (by simp)), ih oldTail newTail]
      rfl
theorem silent_service (fetch : Int64 → Option Decoded) (rxSection : Nat)
    (Q : Executed → Prop) (s : MachineState)
    (localRun : Eventually (historyStep fetch)
      (fun t => Q t ∧ (NoAnchoredReentry t.history ∧ NoAllowedipsReentry t.history)) ⟨s, [s]⟩)
    (front : List MachineState) (events : List Point)
    (observed : observeHistory (edge rxSection) (front ++ [s]) = .ok events) :
    Eventually (historyStep fetch)
      (fun t => ∃ localState tail, Q localState ∧
        t.machine = localState.machine ∧ localState.history = s :: tail ∧
        t.history = front ++ s :: tail ∧
        observeHistory (edge rxSection) t.history = .ok events ∧
        (NoAnchoredReentry localState.history ∧ NoAllowedipsReentry localState.history))
      ⟨s, front ++ [s]⟩ := by
  have prefixed := history_prefix fetch _ ⟨s, [s]⟩ [s] ⟨[], rfl⟩ localRun
  have joined := history_prepend fetch _ _ prefixed front
  apply eventually_weaken (historyStep fetch) _ _ _ _ joined
  rintro t ⟨localState, ⟨⟨good, noReentry⟩, tail, initialPrefix⟩, machine, history⟩
  have localHistory : localState.history = s :: tail := initialPrefix.symm
  refine ⟨localState, tail, good, machine, localHistory, ?_, ?_, noReentry⟩
  · simpa only [localHistory] using history
  · rw [history, localHistory, observeHistory_splice, observed]
    have empty := no_reentry_observations rxSection localState.history noReentry.1 noReentry.2
    rw [localHistory] at empty
    rw [empty]
    exact congrArg Except.ok (List.append_nil events)



/-- The reusable observer agrees with the global M2 observer once each
observed helper return carries the checked caller PC. -/
theorem global_edge (rxSection : Nat) (before after : MachineState) (points : List Point)
    (observed : edge rxSection before after = .ok points)
    (returns : ∀ point ∈ points, point.tag = .returned "wg_peer_get_maybe_zero" →
      point.machine.pc = AllowedipsImage.Lookup.entry+0x119) :
    AllowedipsObservation.edge rxSection before after = .ok points := by
  by_cases inside : Image.PeerGet.entry ≤ before.pc ∧ before.pc < Image.PeerGet.entry+0xe4
  · have avoid (pc : Int64) (apart : ¬(Image.PeerGet.entry ≤ pc ∧ pc < Image.PeerGet.entry+0xe4)) : before.pc ≠ pc := by
      intro eq
      exact apart (eq ▸ inside)
    have nLookup41 := avoid (AllowedipsImage.Lookup.entry+0x41) (by decide)
    have nLookup5b := avoid (AllowedipsImage.Lookup.entry+0x5b) (by decide)
    have nLookup81 := avoid (AllowedipsImage.Lookup.entry+0x81) (by decide)
    have nLookupd3 := avoid (AllowedipsImage.Lookup.entry+0xd3) (by decide)
    have nLookupff := avoid (AllowedipsImage.Lookup.entry+0xff) (by decide)
    have nLookup9b := avoid (AllowedipsImage.Lookup.entry+0x9b) (by decide)
    have nLookupb2 := avoid (AllowedipsImage.Lookup.entry+0xb2) (by decide)
    have nLookup109 := avoid (AllowedipsImage.Lookup.entry+0x109) (by decide)
    have nLookup11c := avoid (AllowedipsImage.Lookup.entry+0x11c) (by decide)
    have nLookupe5 := avoid (AllowedipsImage.Lookup.entry+0xe5) (by decide)
    have nLookup114 := avoid (AllowedipsImage.Lookup.entry+0x114) (by decide)
    have nLookup14e := avoid (AllowedipsImage.Lookup.entry+0x14e) (by decide)
    have nCommonBits24 := avoid (AllowedipsImage.CommonBits.entry+0x24) (by decide)
    have nCommonBits3c := avoid (AllowedipsImage.CommonBits.entry+0x3c) (by decide)
    have nCommonBits91 := avoid (AllowedipsImage.CommonBits.entry+0x91) (by decide)
    have nCommonBits4b := avoid (AllowedipsImage.CommonBits.entry+0x4b) (by decide)
    have nCommonBits74 := avoid (AllowedipsImage.CommonBits.entry+0x74) (by decide)
    have nCommonBitsc3 := avoid (AllowedipsImage.CommonBits.entry+0xc3) (by decide)
    have old := observed
    simp [edge, inside] at old
    by_cases ret : before.pc = Image.PeerGet.entry+0xaf
    · have returned : points = [LookupObservation.returned "wg_peer_get_maybe_zero" after] := by
        have h := old.symm
        simp only [LookupObservation.edge, ret, Image.Lookup.entry, Image.PeerGet.entry] at h
        change Except.ok points = Except.ok [LookupObservation.returned "wg_peer_get_maybe_zero" after] at h
        exact Except.ok.inj h
      have target := returns (LookupObservation.returned "wg_peer_get_maybe_zero" after) (by simp [returned]) rfl
      change after.pc = AllowedipsImage.Lookup.entry+0x119 at target
      simp [AllowedipsObservation.edge, ret, returned, target, Image.PeerGet.entry,
        AllowedipsImage.Lookup.entry, AllowedipsImage.CommonBits.entry]
      rfl
    · simp only [AllowedipsObservation.edge, nLookup41, nLookup5b, nLookup81, nLookupd3, nLookupff, nLookup9b, nLookupb2, nLookup109, nLookup11c, nLookupe5, nLookup114, nLookup14e, nCommonBits24, nCommonBits3c, nCommonBits91, nCommonBits4b, nCommonBits74, nCommonBitsc3, ret, false_or, ite_false]
      cases mapped : (Image.fetchIn Image.PeerGet.entry Image.PeerGet.code before.pc).isSome with
      | true => simpa only [mapped, ite_true] using old
      | false =>
        have avoidPeer (pc : Int64) (yes : (Image.fetchIn Image.PeerGet.entry Image.PeerGet.code pc).isSome = true) : before.pc ≠ pc := by
          intro eq
          rw [← eq, mapped] at yes
          cases yes
        have p15 := avoidPeer (Image.PeerGet.entry+0x15) (by decide)
        have p3d := avoidPeer (Image.PeerGet.entry+0x3d) (by decide)
        have p63 := avoidPeer (Image.PeerGet.entry+0x63) (by decide)
        have p79 := avoidPeer (Image.PeerGet.entry+0x79) (by decide)
        have p8d := avoidPeer (Image.PeerGet.entry+0x8d) (by decide)
        have p94 := avoidPeer (Image.PeerGet.entry+0x94) (by decide)
        have pb5 := avoidPeer (Image.PeerGet.entry+0xb5) (by decide)
        have pc3 := avoidPeer (Image.PeerGet.entry+0xc3) (by decide)
        have pd4 := avoidPeer (Image.PeerGet.entry+0xd4) (by decide)
        have l32 := avoid (Image.Lookup.entry+0x32) (by decide)
        have l6a := avoid (Image.Lookup.entry+0x6a) (by decide)
        have l5c := avoid (Image.Lookup.entry+0x5c) (by decide)
        have lab := avoid (Image.Lookup.entry+0xab) (by decide)
        have lb5 := avoid (Image.Lookup.entry+0xb5) (by decide)
        have lc3 := avoid (Image.Lookup.entry+0xc3) (by decide)
        have l94 := avoid (Image.Lookup.entry+0x94) (by decide)
        have empty : LookupObservation.edge rxSection before after = .ok [] := by
          simp only [LookupObservation.edge, p15, p3d, p63, p79, p8d, p94, pb5, pc3, pd4, l32, l6a, l5c, lab, lb5, lc3, l94, ret, false_or, ite_false]
          rfl
        have he : points = [] := Except.ok.inj (old.symm.trans empty)
        simp only [ he, Bool.false_eq_true, ite_false]
        rfl
  · simpa only [edge, inside, ite_false] using observed


/-- Lift edge agreement to the retained actual history. -/
theorem global_history (rxSection : Nat) (history : List MachineState) (points : List Point)
    (observed : observeHistory (edge rxSection) history = .ok points)
    (returns : ∀ point ∈ points, point.tag = .returned "wg_peer_get_maybe_zero" →
      point.machine.pc = AllowedipsImage.Lookup.entry+0x119) :
    observeHistory (AllowedipsObservation.edge rxSection) history = .ok points := by
  induction history generalizing points with
  | nil => exact observed
  | cons before rest ih =>
    cases rest with
    | nil => exact observed
    | cons after rest =>
      change (do
        let here ← edge rxSection before after
        let later ← observeHistory (edge rxSection) (after :: rest)
        pure (here ++ later)) = .ok points at observed
      cases first : edge rxSection before after with
      | error e =>
        rw [first] at observed
        change Except.error e = Except.ok points at observed
        cases observed
      | ok here =>
        cases later : observeHistory (edge rxSection) (after :: rest) with
        | error e =>
          rw [first, later] at observed
          change Except.error e = Except.ok points at observed
          cases observed
        | ok tail =>
          have he : here ++ tail = points := by
            rw [first, later] at observed
            change Except.ok (here ++ tail) = Except.ok points at observed
            exact Except.ok.inj observed
          have headGlobal := global_edge rxSection before after here first
            (fun point member tag => returns point (he ▸ List.mem_append_left tail member) tag)
          have tailGlobal := ih tail later
            (fun point member tag => returns point (he ▸ List.mem_append_right here member) tag)
          change (do
            let here ← AllowedipsObservation.edge rxSection before after
            let later ← observeHistory (AllowedipsObservation.edge rxSection) (after :: rest)
            pure (here ++ later)) = .ok points
          rw [headGlobal, tailGlobal]
          exact congrArg Except.ok he

end Binary.AllowedipsPeerObservation
