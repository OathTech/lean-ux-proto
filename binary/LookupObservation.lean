import History
import Image
import MirrorHistory

namespace Binary.LookupObservation
open Leanux

/-- An observed point holds an actual Kraken state, never a supplied mirror
    World. Decision records are computed from this execution's edges. -/
structure Point where
  tag : MirrorHistory.Tag
  machine : MachineState
  step : Option Step := none

def decision (rxSection : Nat) (d : Decision) (outcome : Bool) (machine : MachineState)
    (operands : Option (Int × Int) := none) : Point :=
  ⟨.decision d, machine, some {decision := d, outcome, operands, netRx := rxSection}⟩

def call (symbol : String) (machine : MachineState) : Point :=
  ⟨.call symbol, machine, none⟩

def returned (symbol : String) (machine : MachineState) : Point :=
  ⟨.returned symbol, machine, none⟩

/-- A declared conditional edge has exactly its two decoded successors.
    A different successor is an observation error, not a false outcome. -/
def choice (next yes no : Int64) : Except String Bool :=
  if next = yes then .ok true
  else if next = no then .ok false
  else .error "unexpected successor at a lookup correspondence point"

/-- Observer for lookup and its peer-get helper. The rxSection is a shared
    incoming trace context. No expected decision stream or mirror World is
    an argument. Multiple emitted decisions account for compiler-merged
    exits; repeated visits remain repeated events. -/
def edge (rxSection : Nat) (s t : MachineState) : Except String (List Point) := do
  let l := Image.Lookup.entry
  let p := Image.PeerGet.entry
  if s.pc = l + 0x32 ∨ s.pc = l + 0x6a then
    let more ← choice t.pc (l + 0x34) (l + 0x6c)
    return [decision rxSection .idxWalk more t] ++
      (if more then [] else [decision rxSection .idxFound false t])
  if s.pc = l + 0x5c then
    let hit ← choice t.pc (l + 0x95) (l + 0x5e)
    return [decision rxSection .idxMatch hit t]
  if s.pc = l + 0xab then
    let good ← choice t.pc (l + 0xad) (l + 0x71)
    return [decision rxSection .idxTypeMatch good t, decision rxSection .idxFound good t]
  if s.pc = l + 0xb5 then
    if t.pc != p then throw "lookup's peer-get call reached a different callee"
    return [call "wg_peer_get_maybe_zero" t]
  if s.pc = l + 0xc3 then
    let live ← choice t.pc (l + 0xc5) (l + 0x71)
    return [decision rxSection .idxPeerAlive live t]
  if s.pc = l + 0x94 then return [returned "wg_index_hashtable_lookup" t]
  if s.pc = p + 0x15 then
    let null ← choice t.pc (p + 0xdd) (p + 0x1b)
    return [decision rxSection .peerGetMaybeZeroNull null t]
  if s.pc = p + 0x3d then
    let zero ← choice t.pc (p + 0xb0) (p + 0x3f)
    let old := (s.data.regs.get (.low .rbp .W32)).toNat
    return [decision rxSection .refcountAddNzZero zero t (some (old, 0))]
  if s.pc = p + 0x63 then
    let retry ← choice t.pc (p + 0xf2) (p + 0x69)
    return [decision rxSection .refcountAddNzRetry retry t]
  if s.pc = p + 0x79 then
    let negative ← choice t.pc (p + 0xe1) (p + 0x7b)
    return [decision rxSection .refcountAddNzNegative negative t]
  if s.pc = p + 0x8d then
    let wraps ← choice t.pc (p + 0xe1) (p + 0x8f)
    return [decision rxSection .refcountAddNzWraps wraps t]
  if s.pc = p + 0x94 then
    return [decision rxSection .peerGetMaybeZeroDead
      (s.data.regs.get (.low .rbp .W32) == 0) t]
  if s.pc = p + 0xb5 then return [decision rxSection .refcountAddNzNegative false t]
  if s.pc = p + 0xc3 then return [decision rxSection .refcountAddNzWraps false t]
  if s.pc = p + 0xd4 then return [decision rxSection .peerGetMaybeZeroDead true t]
  if s.pc = p + 0xaf then return [returned "wg_peer_get_maybe_zero" t]
  return []

def observe (rxSection : Nat) (history : List MachineState) : Except String (List Point) := do
  let initial :: _ := history | throw "empty lookup execution history"
  if initial.pc != Image.Lookup.entry then throw "lookup history does not start at its entry"
  return call "wg_index_hashtable_lookup" initial :: (← observeHistory (edge rxSection) history)

/-- Matching includes exact tag, order (via MatchesPoints), and decision record.
    The state relation is supplied by the function-specific physical proof;
    this definition does not turn an arbitrary relation into adequacy. -/
def MatchesPoint (R : MachineState → World → Prop) (actual : Point)
    (mirror : MirrorHistory.Point) : Prop :=
  actual.tag = mirror.tag ∧ R actual.machine mirror.world ∧
    match actual.step with
    | none => True
    | some step => mirror.world.steps.back? = some step

/-- Pointwise correspondence with equal lengths and order. -/
inductive MatchesPoints (R : MachineState → World → Prop) :
    List Point → List MirrorHistory.Point → Prop where
  | nil : MatchesPoints R [] []
  | cons {actual mirror actuals mirrors} :
      MatchesPoint R actual mirror → MatchesPoints R actuals mirrors →
      MatchesPoints R (actual :: actuals) (mirror :: mirrors)

theorem MatchesPoints.length_eq {R actual mirror} (h : MatchesPoints R actual mirror) :
    actual.length = mirror.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem MatchesPoints.take {R actual mirror} (h : MatchesPoints R actual mirror) (n : Nat) :
    MatchesPoints R (actual.take n) (mirror.take n) := by
  induction h generalizing n with
  | nil => simpa using (MatchesPoints.nil (R := R))
  | cons head tail ih =>
    cases n with
    | zero => exact .nil
    | succ n => exact .cons head (ih n)

/-- The matched semantic events form the exact corresponding source prefix.
    Counting events without checking their tags, records and states would not
    justify choosing a source World for an intermediate machine cut. -/
def PrefixMatches (R : MachineState → World → Prop) (actual : List Point)
    (source : List MirrorHistory.Point) : Prop :=
  actual.length ≤ source.length ∧
    MatchesPoints R actual (source.take actual.length)

theorem prefix_of_append {R front rest source}
    (h : MatchesPoints R (front ++ rest) source) : PrefixMatches R front source := by
  have lengths := h.length_eq
  refine ⟨?_, ?_⟩
  · simp only [List.length_append] at lengths
    omega
  · simpa only [List.take_left] using h.take front.length

/-- Stuttering correspondence at every anchored region/call/comparison cut.
    The active source World is determined by an exact matched prefix of the
    fixed accepted run. Service-internal PCs are deliberately outside this
    domain; their contracts must exclude additional anchored observations.
    Pending writes and temporary registers belong to the phase equations of
    R. This is a proof obligation, not an axiom or an established invariant. -/
def CutsAligned (R : MachineState → World → Prop) (rxSection : Nat)
    (history : List MachineState) (source : List MirrorHistory.Point) : Prop :=
  ∀ i current, history[i]? = some current → current.pc ∈ Image.cutPoints →
    ∃ events last,
      observe rxSection (history.take (i + 1)) = .ok events ∧
      PrefixMatches R events source ∧
      (source.take events.length).getLast? = some last ∧
      R current last.world

/-- Exact semantic history plus all anchored stuttering cuts. Return
    destination, result registers and saved frame are separate postconditions
    of the function theorem, not consequences of a return tag. -/
def MatchesRun {α : Type} (R : MachineState → World → Prop) (rxSection : Nat)
    (executed : Executed) (source : MirrorHistory.Run α) : Prop :=
  ∃ points, observe rxSection executed.history = .ok points ∧
    MatchesPoints R points source.points ∧
    CutsAligned R rxSection executed.history source.points ∧
    R executed.machine source.finalWorld

#print axioms MatchesPoints.length_eq
#print axioms prefix_of_append
end Binary.LookupObservation
