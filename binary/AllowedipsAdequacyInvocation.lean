import AllowedipsAdequacyOuterCount
import AllowedipsAdequacyPost

namespace Binary.AllowedipsRelation
open Leanux LookupObservation
open AllowedipsOuterCount (isOuter)

def observedReturns (points : List Point) : Nat :=
  points.countP (fun p => isOuter p.tag)

def rawReturns (history : List MachineState) : Nat :=
  history.countP (fun s => s.pc == AllowedipsImage.Lookup.entry+0x14e)

theorem matched_returns {R seen points source}
    (matched : MatchesPointsFrom R seen points source) :
    observedReturns points = AllowedipsOuterCount.total source := by
  induction matched with
  | nil => rfl
  | cons head tail ih =>
    simp only [observedReturns, List.countP_cons] at ih ⊢
    simp only [AllowedipsOuterCount.total, List.filter_cons, head.1]
    split <;> simp_all [AllowedipsOuterCount.total]

theorem raw_return_bound (rx : Nat) (history : List MachineState) (points : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rx) history = .ok points) :
    rawReturns history.dropLast ≤ observedReturns points := by
  induction history generalizing points with
  | nil => simp [rawReturns]
  | cons s rest ih =>
    cases rest with
    | nil => simp [rawReturns]
    | cons t rest =>
      cases first : AllowedipsObservation.edge rx s t with
      | error e => simp [observeHistory, first] at observed; cases observed
      | ok delta =>
        cases next : observeHistory (AllowedipsObservation.edge rx) (t :: rest) with
        | error e => simp [observeHistory, first, next] at observed; cases observed
        | ok later =>
          have eq : delta ++ later = points := by
            simp only [observeHistory, first, next] at observed
            exact Except.ok.inj observed
          subst points
          have bound := ih later next
          by_cases ret : s.pc = AllowedipsImage.Lookup.entry+0x14e
          · have emitted : delta = [returned "lookup" t] := by
              have e : AllowedipsObservation.edge rx s t = .ok [returned "lookup" t] := by
                simp [AllowedipsObservation.edge, ret, AllowedipsImage.Lookup.entry, AllowedipsImage.CommonBits.entry]
                rfl
              exact Except.ok.inj (first.symm.trans e)
            simp only [List.dropLast_cons_cons, rawReturns, List.countP_cons,
              observedReturns, List.countP_append] at bound ⊢
            simp [ret, emitted, returned, isOuter] at bound ⊢
            omega
          · simp only [List.dropLast_cons_cons, rawReturns, List.countP_cons,
              observedReturns, List.countP_append] at bound ⊢
            simp [ret]
            omega

theorem observed_return_bound (rx : Nat) (history : List MachineState) (points : List Point)
    (observed : AllowedipsObservation.observe rx history = .ok points) :
    rawReturns history.dropLast ≤ observedReturns points := by
  cases history with
  | nil => cases observed
  | cons initial rest =>
    by_cases pc : initial.pc = AllowedipsImage.Lookup.entry
    · cases raw : observeHistory (AllowedipsObservation.edge rx) (initial :: rest) with
      | error e => simp [AllowedipsObservation.observe, pc, raw] at observed; cases observed
      | ok later =>
        have eq : call "lookup" initial :: later = points := by
          simp [AllowedipsObservation.observe, pc, raw] at observed
          exact Except.ok.inj observed
        rw [← eq]
        simpa [observedReturns, call, isOuter] using raw_return_bound rx (initial :: rest) later raw
    · simp [AllowedipsObservation.observe, pc] at observed; cases observed

theorem no_early_return (rx : Nat) (history : List MachineState) (points : List Point)
    (source : List MirrorHistory.Point) {rel : Relation}
    (observed : AllowedipsObservation.observe rx history = .ok points) (matched : MatchesPoints rel points source)
    (one : AllowedipsOuterCount.total source = 1)
    (ended : EndsAtReturn (AllowedipsImage.Lookup.entry+0x14e) history) :
    NoEarlyReturn (AllowedipsImage.Lookup.entry+0x14e) history := by
  obtain ⟨front, before, after, shape, last⟩ := ended
  have bound := observed_return_bound rx history points observed
  rw [matched_returns matched, one, shape] at bound
  have absent : ∀ s ∈ front, s.pc ≠ AllowedipsImage.Lookup.entry+0x14e := by
    simpa [rawReturns, List.dropLast_append_of_ne_nil, List.countP_append, last] using bound
  simpa [NoEarlyReturn, shape, List.dropLast_append_of_ne_nil] using absent

theorem AllowedipsPost.noEarly (c : Config) (coverage : TrustBase.KcovLayout)
    (preempt : BitVec 32) (ra : UInt64) (initial : MachineState) (world : World)
    (answer : Option WG.PeerId) (finalWorld : World) (final : Executed)
    (post : AllowedipsPost c coverage preempt ra initial world answer finalWorld final) :
    NoEarlyReturn (AllowedipsImage.Lookup.entry+0x14e) final.history := by
  obtain ⟨_, _, v, points, source, _, _, accepted, observed, matched, _, _, _, _, _, _, ended⟩ := post
  exact no_early_return c.rxSection final.history points source observed matched
    (AllowedipsOuterCount.lookup_total c.root c.bits c.key world finalWorld answer source accepted) ended

end Binary.AllowedipsRelation
