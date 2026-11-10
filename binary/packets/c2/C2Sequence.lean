import C2Test

/-! Result C2: executed tests of the sequence statements of the final text
(`NoCounterAcceptedTwice`, `ReplayWitness`, `ReplayRefused`, and the floor and
advance behaviours that the statement file no longer states), the `bts` run by Kraken's
interpreter. Not proofs.

A list of packet counters is run through the range visit by visit. Between visits only
the 1032 window bytes are carried over: every other byte and register is rebuilt, and
the coverage mode and preempt count change from visit to visit. The accepted counters
are compared with the mirror's `counterValidate` called in sequence on one world. -/
namespace Binary.C2.Sequence
open Binary TrustBase Leanux Binary.C2.Test
local instance : Labels := Binary.Image.linkedLabels

/-- What happens to the window between two visits. -/
inductive Between where
  | retained
  /-- The premise `WindowRetained` broken: the window is zeroed after visit `n`. -/
  | zeroedAfter (n : Nat)

/-- Callbacks, coverage mode, records present and preempt count of visit `i`. -/
def setting (i : Nat) : Callbacks × Nat × Nat × Nat :=
  match i % 4 with
  | 0 => (.image, 0, 0, 0x100)
  | 1 => (.image, 3, 5, 0x300)
  | 2 => (.scramble, 0, 0, 0xfffffe00)
  | _ => (.image, 2, 60, 0x100)

/-- Run the visits; return (packet counter, accepted) per visit. -/
def machine (bts : Bts) (between : Between) (start : Setup) (nonces : List Nat) :
    Except String (List (Nat × Bool)) := do
  let mut previous : Option DataMem := none
  let mut out := []
  let mut i := 0
  for nonce in nonces do
    let (callbacks, mode, recorded, preempt) := setting i
    let c : Setup := { start with nonce, mode, recorded, preempt }
    let s := initial c previous
    let (t, _) ← run callbacks bts (0x1234567 * (UInt64.ofNat i + 1)) s
    kept {} c s t
    out := out ++ [(nonce, accepted t)]
    previous := some (match between with
      | .zeroedAfter n => if i == n then memory { start with counter := 0, bitmap := .zero } else t.data.dmem
      | .retained => t.data.dmem)
    i := i + 1
  return out

/-- The mirror's function called in sequence, the replay state threaded. -/
def mirrorSequence (start : Setup) (nonces : List Nat) : Except String (List (Nat × Bool)) := do
  let mut rc : WG.ReplayCounter := { counter := start.counter, backtrack := bitmapOf start.bitmap }
  let mut out := []
  for nonce in nonces do
    let (result, next) ← mirror rc nonce
    out := out ++ [(nonce, result)]
    rc := next
  return out

def acceptedOf (visits : List (Nat × Bool)) : List Nat := (visits.filter (·.2)).map (·.1)

def nodup : List Nat → Bool
  | [] => true
  | a :: rest => !rest.contains a && nodup rest

def withinWindow : List Nat → Bool
  | [] => true
  | a :: rest => rest.all (fun later => a ≤ later + 8128) && withinWindow rest

/-- Pseudo-random counters with many repeats, drifting upward, with occasional jumps. -/
def drifting (seed count : Nat) : List Nat := Id.run do
  let mut x := seed
  let mut base := 0
  let mut out := []
  for _ in [:count] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2^64
    let r := x / 2^33
    if r % 23 == 0 then base := base + 5000 + r % 9000
    else if r % 5 == 0 then base := base + r % 70
    out := out ++ [base + r % 40 - (if base > 200 && r % 7 == 0 then r % 200 else 0)]
  return out

def sequences : List (String × Setup × List Nat) :=
  [("the landed boundary witness", { counter := 0, nonce := 0, bitmap := .zero }, [8129, 1, 0, 1]),
   ("small with replays", { counter := 0, nonce := 0, bitmap := .zero }, [0, 1, 2, 1, 0, 5, 5, 3, 70, 3, 69, 70, 4]),
   ("drifting, zero window", { counter := 0, nonce := 0, bitmap := .zero }, drifting 1 160),
   ("drifting, second seed", { counter := 0, nonce := 0, bitmap := .zero }, drifting 77 160),
   ("drifting, arbitrary window bytes", { counter := 90, nonce := 0, bitmap := .pattern }, drifting 5 120),
   ("near the limit", { counter := 0xffffffffffffe000, nonce := 0, bitmap := .zero },
      [0xffffffffffffe03c, 0xffffffffffffe03d, 0xffffffffffffe03d, 0xffffffffffffe03e, 0xffffffffffffe010,
       0xffffffffffffe03c, 5, 0xffffffffffffffff])]

def verdict (bts : Bts) (between : Between) (name : String) (start : Setup) (nonces : List Nat) :
    Except String String := do
  let visits ← machine bts between start nonces
  let expected ← mirrorSequence start nonces
  let acc := acceptedOf visits
  unless nodup acc do throw s!"{name}: a counter is accepted twice"
  unless withinWindow acc do throw s!"{name}: an accepted counter is more than a window behind"
  unless visits == expected do throw s!"{name}: differs from the mirror called in sequence"
  return s!"{name}: {nonces.length} visits, {acc.length} accepted"

/-- Wrong variants, with whether the sequence checks are expected to catch them.
The third is a finding about the checks, kept as a test: a `bts` that consistently
tests and sets the neighbouring bit of the same word is a rotation of each word's bits,
so every sequence of acceptances is unchanged. The machine-level clauses do not depend
on which bit of the word is used; only the comparison of the bytes with the mirror
(`C2Test`) rejects that variant. -/
def wrongRuns : List (String × Bts × Between × Bool) :=
  [("bts does not write the quadword back", .noStore, .retained, true),
   ("bts reports the new bit", .carryNewBit, .retained, true),
   ("bts uses the next bit, consistently", .bitPlusOne, .retained, false),
   ("window zeroed between visits (premise broken)", .real, .zeroedAfter 5, true)]

def zeroWindow : Setup := { counter := 0, nonce := 0, bitmap := .zero }

-- Printed, and the compilation fails on any surprise.
#eval show IO Unit from do
  for (name, start, nonces) in sequences do
    match verdict .real .retained name start nonces with
    | .ok line => IO.println line
    | .error e => throw (IO.userError e)
  -- `ReplayWitness`, concretely: the same counter twice on a zeroed window.
  let twice := (machine .real .retained zeroWindow [41, 41]).toOption
  IO.println s!"the same counter twice on a zeroed window: {twice}"
  unless twice == some [(41, true), (41, false)] do throw (IO.userError "the replay witness fails")
  -- The witness's extension (review finding F1), concretely: the first visit's window
  -- bytes represent a replay state, a world holds it, and the mirror's own
  -- `counterValidate` on that world succeeds and accepts.
  let first := initial { zeroWindow with nonce := 41 }
  match (represented {} first.data.dmem) >>= (fun c => (mirror c 41).map fun r => (c, r)) with
  | .ok (c, (true, _)) =>
    unless windowOf (worldOf c) 0 == some c do throw (IO.userError "the witness's world does not hold the state")
    IO.println s!"the first visit's window represents counter {c.counter} with {c.backtrack.size} words; the mirror's run on a world holding it succeeds and accepts"
  | .ok (_, (false, _)) => throw (IO.userError "the mirror refuses the witness's first visit")
  | .error e => throw (IO.userError s!"the witness's mirror run fails: {e}")
  -- An advancing counter is accepted, concretely: every bitmap bit set, counters in a later word.
  for (counter, nonce) in [(100, 128), (100, 64*200 + 7), (0xffffffffffffdfc0, 0xffffffffffffe03d), (0, 64)] do
    let one := (machine .real .retained { counter, nonce, bitmap := .ones } [nonce]).toOption
    unless one == some [(nonce, true)] do
      throw (IO.userError s!"an advancing counter is refused: {counter} {nonce}")
  IO.println "advancing counters over an all-ones bitmap: 4 of 4 accepted"
  for (name, bts, between, expected) in wrongRuns do
    let caught := sequences.filterMap fun (n, start, nonces) =>
      match verdict bts between n start nonces with
      | .ok _ => none
      | .error e => some e
    IO.println s!"wrong variant, {name}: caught on {caught.length} of {sequences.length} sequences; first: {caught.head?}"
    unless caught.isEmpty != expected do
      throw (IO.userError s!"wrong variant, unexpected outcome: {name}")

end Binary.C2.Sequence
