import LookupOuterCount
import LookupPost

namespace Binary.LookupRelation
open Leanux LookupObservation
open LookupOuterCount (isOuter)

def observedReturns (points : List Point) : Nat :=
  points.countP (fun p => isOuter p.tag)

def rawReturns (history : List MachineState) : Nat :=
  history.countP (fun s => s.pc == Image.Lookup.entry+0x94)

theorem matched_returns {R seen points source}
    (matched : MatchesPointsFrom R seen points source) :
    observedReturns points = LookupOuterCount.total source := by
  induction matched with
  | nil => rfl
  | cons head tail ih =>
    simp only [observedReturns, List.countP_cons] at ih ⊢
    simp only [LookupOuterCount.total, List.filter_cons, head.1]
    split <;> simp_all [LookupOuterCount.total]

theorem raw_return_bound (rx : Nat) (history : List MachineState) (points : List Point)
    (observed : observeHistory (edge rx) history = .ok points) :
    rawReturns history.dropLast ≤ observedReturns points := by
  induction history generalizing points with
  | nil => simp [rawReturns]
  | cons s rest ih =>
    cases rest with
    | nil => simp [rawReturns]
    | cons t rest =>
      cases first : edge rx s t with
      | error e => simp [observeHistory, first] at observed; cases observed
      | ok delta =>
        cases next : observeHistory (edge rx) (t :: rest) with
        | error e => simp [observeHistory, first, next] at observed; cases observed
        | ok later =>
          have eq : delta ++ later = points := by
            simp only [observeHistory, first, next] at observed
            exact Except.ok.inj observed
          subst points
          have bound := ih later next
          by_cases ret : s.pc = Image.Lookup.entry+0x94
          · have emitted : delta = [returned "wg_index_hashtable_lookup" t] := by
              have e : edge rx s t = .ok [returned "wg_index_hashtable_lookup" t] := by
                simp [edge, ret, Image.Lookup.entry, Image.PeerGet.entry]
                rfl
              exact Except.ok.inj (first.symm.trans e)
            simp only [List.dropLast_cons_cons, rawReturns, List.countP_cons,
              observedReturns, List.countP_append] at bound ⊢
            simp [ret, emitted, returned, isOuter, observedReturns] at bound ⊢
            omega
          · simp only [List.dropLast_cons_cons, rawReturns, List.countP_cons,
              observedReturns, List.countP_append] at bound ⊢
            simp [ret]
            omega

theorem observed_return_bound (rx : Nat) (history : List MachineState) (points : List Point)
    (observed : observe rx history = .ok points) :
    rawReturns history.dropLast ≤ observedReturns points := by
  cases history with
  | nil => cases observed
  | cons initial rest =>
    by_cases pc : initial.pc = Image.Lookup.entry
    · cases raw : observeHistory (edge rx) (initial :: rest) with
      | error e => simp [observe, pc, raw] at observed; cases observed
      | ok later =>
        have eq : call "wg_index_hashtable_lookup" initial :: later = points := by
          simp [observe, pc, raw] at observed
          exact Except.ok.inj observed
        rw [← eq]
        simpa [observedReturns, call, isOuter] using raw_return_bound rx (initial :: rest) later raw
    · simp [observe, pc] at observed; cases observed

theorem no_early_return (rx : Nat) (history : List MachineState) (points : List Point)
    (source : List MirrorHistory.Point) {rel : Relation}
    (observed : observe rx history = .ok points) (matched : MatchesPoints rel points source)
    (one : LookupOuterCount.total source = 1)
    (ended : EndsAtReturn (Image.Lookup.entry+0x94) history) :
    NoEarlyReturn (Image.Lookup.entry+0x94) history := by
  obtain ⟨front, before, after, shape, last⟩ := ended
  have bound := observed_return_bound rx history points observed
  rw [matched_returns matched, one, shape] at bound
  have absent : ∀ s ∈ front, s.pc ≠ Image.Lookup.entry+0x94 := by
    simpa [rawReturns, List.dropLast_append_of_ne_nil, List.countP_append, last] using bound
  simpa [NoEarlyReturn, shape, List.dropLast_append_of_ne_nil] using absent

theorem LookupPost.noEarly (c : Config) (coverage : TrustBase.KcovLayout)
    (preempt : BitVec 32) (ra : UInt64) (initial : MachineState) (world : World)
    (answer : Option (WG.IndexOwner × WG.PeerId)) (finalWorld : World) (final : Executed)
    (post : LookupPost c coverage preempt ra initial world answer finalWorld final) :
    NoEarlyReturn (Image.Lookup.entry+0x94) final.history := by
  obtain ⟨_, _, v, points, source, _, _, accepted, observed, matched, _, _, _, _, _, _, ended⟩ := post
  exact no_early_return c.rxSection final.history points source observed matched
    (LookupOuterCount.lookup_total c.kinds c.query world finalWorld answer source accepted) ended

end Binary.LookupRelation
