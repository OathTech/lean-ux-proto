import Leanux.Proofs.WG.Index.Table

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

abbrev LookupState := Option IndexEntry × Bool

def lookupStep (kinds : List IndexKind) (index : Nat) (e : IndexEntry)
    (state : LookupState) : M (ForInStep LookupState) := do
  _ ← branch .idxWalk true
  if ← branch .idxMatch (e.index == index) then
    let permitted ← branch .idxTypeMatch (kinds.contains e.kind)
    return .done (if permitted then some e else state.1, true)
  return .yield state

def lookupFinish (state : LookupState) : M (Option (IndexOwner × PeerId)) := do
  let (entry, stopped) := state
  if !stopped then _ ← branch .idxWalk false
  if ← branch .idxFound entry.isSome then
    let some e := entry | invariant "unreachable"
    let peer ← peerGetMaybeZero (← e.owner.peerWord)
    e.owner.setPeerWord peer
    if ← branch .idxPeerAlive peer.isSome then
      let some pid := peer | invariant "unreachable"
      return some (e.owner, pid)
  return none

theorem indexLookup_source (kinds : List IndexKind) (index : Nat) :
    indexLookup kinds index = (do
      let entries ← indexBucket index
      let state ← forIn entries (none, false) (lookupStep kinds index)
      lookupFinish state) := by
  simp only [indexLookup, lookupStep, lookupFinish]
  congr 1
  funext entries
  congr 1
  congr 1
  funext e state
  congr 1
  funext u
  congr 1
  funext matched
  split
  · congr 1
    funext permitted
    split <;> rfl
  · rfl

/-- Selection stops at the first equal numeric index, even if its kind is excluded. -/
def selectedState (kinds : List IndexKind) (index : Nat) (entries : List IndexEntry)
    (initial : LookupState) : LookupState :=
  match entries.find? (·.index == index) with
  | none => initial
  | some e => (if kinds.contains e.kind then some e else initial.1, true)

theorem lookupScan_cons (kinds : List IndexKind) (index : Nat) (e : IndexEntry)
    (es : List IndexEntry) (initial : LookupState) :
    forIn (e :: es) initial (lookupStep kinds index) = (do
      _ ← branch .idxWalk true
      _ ← branch .idxMatch (e.index == index)
      if e.index == index then
        _ ← branch .idxTypeMatch (kinds.contains e.kind)
        pure (if kinds.contains e.kind then some e else initial.1, true)
      else forIn es initial (lookupStep kinds index)) := by
  simp [List.forIn_cons, lookupStep, branch, bind_assoc]
  split <;> simp [bind_assoc]

def recordStep (w : World) (decision : Decision) (outcome : Bool) : World :=
  { w with steps := w.steps.push { decision, outcome, netRx := w.netRxSection } }

@[simp] theorem branch_run (w : World) (decision : Decision) (outcome : Bool) :
    (branch decision outcome).run w = .ok (outcome, recordStep w decision outcome) := rfl

@[simp] theorem except_bind_ok {α β : Type} (x : α) (f : α → Except Stop β) :
    (Except.ok x >>= f) = f x := rfl

@[simp] theorem except_map_ok {α β : Type} (x : α) (f : α → β) :
    f <$> (Except.ok x : Except Stop α) = Except.ok (f x) := rfl

theorem lookupScan_returns (kinds : List IndexKind) (index : Nat)
    (entries : List IndexEntry) (initial : LookupState) (k : Kernel) :
    Returns (forIn entries initial (lookupStep kinds index)) (fun w => w.k = k)
      (fun result w => result = selectedState kinds index entries initial ∧ w.k = k) := by
  induction entries generalizing initial k with
  | nil =>
    intro w hw
    exact ⟨initial, w, rfl, rfl, hw⟩
  | cons e es ih =>
    intro w hw
    let next := recordStep (recordStep w .idxWalk true) .idxMatch (e.index == index)
    by_cases matched : e.index = index
    · let final := recordStep next .idxTypeMatch (kinds.contains e.kind)
      refine ⟨(if kinds.contains e.kind then some e else initial.1, true), final, ?_, ?_, hw⟩
      · rw [lookupScan_cons]
        simp [StateT.run_bind, Except.bind, Except.map, branch_run, matched, next, final, StateT.run_pure]
      · simp [selectedState, matched]
    · obtain ⟨result, final, run, selected, kernel⟩ := ih initial k next hw
      refine ⟨result, final, ?_, ?_, kernel⟩
      · rw [lookupScan_cons]
        simpa [StateT.run_bind, Except.bind, Except.map, branch_run, matched, next] using run
      · simpa [selectedState, matched] using selected

end Leanux.Proofs.WG.Index
