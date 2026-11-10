import C2Cut
import C2Test

/-! Executed test of the cut predicates of `binary/C2Cut.lean` against Kraken.

The range, the two 8-byte entries and the landed callback bodies are run instruction by
instruction from the constructed entry states of the statement's tests
(`packets/c2/C2Test.lean`), with the coverage off, in PC mode and in comparison mode.
At every arrival at a cut address the decidable content of the cut predicate is checked
against the machine state: `AtAdvance`, `AtLoop i` (with `i` the number of earlier
arrivals at the loop head), `AtStore`, `AtTail`, and at the exit `AtExit (validate …)`.
Across each of the thirteen calls the content of `CallSite`'s conclusion is checked:
the stack pointer, `%rbx`, `%r12`, `%r13`, `%rbp`, `%r14`, `%r15`, the two spill slots
and the 129 window quadwords are the same after the callback as before the `call`.

A speedbump against a wrong cut (a wrong address, register, slot or window), not a
proof; the propositions of `C2CutInterfaces` are what the packages prove. Compiled by
`binary/packets/c2/proof/check`; in no lake target. -/
namespace Binary.C2.CutTrace
open Binary TrustBase Leanux Binary.C2 Binary.C2.Test
local instance : Labels := Binary.Image.linkedLabels

/-- Offsets of the thirteen `call` instructions from the entry. -/
def callOffsets : List Nat := [31, 49, 64, 82, 109, 123, 151, 161, 207, 219, 253, 263, 280]

def windowOfSetup (c : Setup) : Window :=
  { counter := .ofNat 64 c.counter, words := fun j => .ofNat 64 (c.bitmap.word j) }

/-- The window bytes hold `w` (the executable content of `WindowAt`). -/
def holds (m : Mem 64) (w : Window) : Except String Unit := do
  unless (← readNat m (Test.kp + 136) 8) == w.counter.toNat do throw "window: the counter differs"
  for j in [:128] do
    unless (← readNat m (Test.kp + 136 + 8 + 8 * j) 8) == (w.words j).toNat do
      throw s!"window: word {j} differs"

/-- The executable content of `Carried`, the frame apart (the statement's own tests
compare the frame at the exit). -/
def carried (c : Setup) (s0 : MachineState) (w : Window) (d : MachineData) : Except String Unit := do
  holds d.dmem w
  unless (← readNat d.dmem preemptAddr 4) == (c.preempt + 0x200) % 2 ^ 32 do throw "carried: preempt count"
  unless d.regs.rsp == s0.data.regs.rsp && d.regs.rbx == s0.data.regs.rbx &&
      d.regs.r12 == s0.data.regs.r12 && d.regs.r13 == s0.data.regs.r13 do throw "carried: a kept register"
  for a in [Test.sp - 8, Test.sp + 0x10, Test.sp + 0x18] do
    let _ ← readNat d.dmem a 8

def slot (d : MachineData) (offset : Nat) : Except String Nat := readNat d.dmem (Test.sp + offset) 8

/-- What `CallSite` says is the same after the call. -/
def kept (d : MachineData) : Except String (List Nat) := do
  let mut out := [d.regs.rsp.toNat, d.regs.rbx.toNat, d.regs.r12.toNat, d.regs.r13.toNat,
    d.regs.rbp.toNat, d.regs.r14.toNat, d.regs.r15.toNat, ← slot d 0x10, ← slot d 0x18]
  for i in [:129] do out := (← readNat d.dmem (Test.kp + 136 + 8 * i) 8) :: out
  return out

structure Seen where
  advance : Nat := 0
  loop : Nat := 0
  store : Nat := 0
  tail : Nat := 0
  calls : Nat := 0

def trace (c : Setup) (seed : UInt64) : Except String Seen := do
  let s0 := initial c
  let w := windowOfSetup c
  let nonce : BitVec 64 := .ofNat 64 c.nonce
  let t := nonce + 1
  let mut s := s0
  let mut seen : Seen := {}
  let mut pending : Option (Int64 × List Nat) := none
  for _ in [:60000] do
    if exits.contains s.pc then
      let o := validate w nonce
      unless s.pc == o.exit do throw "exit: not the pivot's"
      unless accepted s == o.accepted do throw "exit: the observation is not the pivot's"
      carried c s0 o.window s.data
      if s.pc == Range.donePC then
        unless s.data.regs.rsi.toNat % 2 ^ 32 == 0x200 do throw "exit: the unlock argument"
      let rejects := decide (Rejects w nonce)
      let ahead := decide (w.counter < t)
      let expect : Nat × Nat × Nat × Nat :=
        if rejects then (0, 0, 0, 0)
        else if ahead then (1, top w t, 1, 1) else (0, 0, 0, 1)
      unless (seen.advance, seen.loop, seen.store, seen.tail) == expect do
        throw s!"cuts visited {(seen.advance, seen.loop, seen.store, seen.tail)}, expected {expect}"
      unless pending.isNone do throw "exit inside a call"
      return seen
    if let some (back, before) := pending then
      if s.pc == back && s.data.regs.rsp == s0.data.regs.rsp then
        unless (← kept s.data) == before do throw s!"call returning to {back}: something kept differs"
        pending := none
    if pending.isNone then
      if s.pc == advancePC then
        carried c s0 w s.data
        unless s.data.regs.rbp.toBitVec == w.counter && s.data.regs.r15.toBitVec == t >>> 6 &&
            (← slot s.data 0x10) == t.toNat do throw "AtAdvance"
        seen := { seen with advance := seen.advance + 1 }
      if s.pc == loopPC then
        let i := seen.loop
        carried c s0 (cleared w i) s.data
        unless i < top w t && s.data.regs.r14.toBitVec == cur w &&
            s.data.regs.rbp.toBitVec == .ofNat 64 (i + 1) &&
            s.data.regs.r15.toBitVec == .ofNat 64 (top w t) &&
            (← slot s.data 0x10) == t.toNat && (← slot s.data 0x18) == (t >>> 6).toNat do
          throw s!"AtLoop {i}"
        seen := { seen with loop := seen.loop + 1 }
      if s.pc == storePC then
        carried c s0 (cleared w (top w t)) s.data
        unless seen.loop == top w t && (← slot s.data 0x10) == t.toNat &&
            (← slot s.data 0x18) == (t >>> 6).toNat do throw "AtStore"
        seen := { seen with store := seen.store + 1 }
      if s.pc == tailPC then
        carried c s0 (if w.counter < t then advance w t else w) s.data
        unless (← slot s.data 0x10) == t.toNat && (← slot s.data 0x18) == (t >>> 6).toNat do
          throw "AtTail"
        seen := { seen with tail := seen.tail + 1 }
      if callOffsets.any (fun offset => s.pc == Range.entry + .ofNat offset) then
        -- from +14 on the carried invariant holds at every call, for the window in progress
        pending := some (s.pc + 5, ← kept s.data)
        seen := { seen with calls := seen.calls + 1 }
    let some i := fetchAll s.pc | throw s!"no instruction at {s.pc}"
    s ← effects seed s 1 (i.instruction.interp s.data ⟨s.pc, s.pc + .ofNat i.size⟩
      (fun d => .done ⟨d, s.pc + .ofNat i.size⟩) (fun p d => .done ⟨d, p⟩))
  throw "instruction budget exhausted"

/-- Stored and packet counters: every branch of the range, slides of 0, 1, 2, 127, 128
and more words, wrap of the word index, and the limits. -/
def counterCases : List (Nat × Nat) :=
  [(0, 0), (1, 0), (5, 3), (5, 4), (5, 5), (63, 62), (63, 63), (64, 63), (100, 200), (100, 8291),
   (100, 8292), (100, 8300), (100, 20000), (8127, 8190), (8191, 8192), (9000, 800), (9000, 871),
   (9000, 872), (16383, 16384), (70000, 61871), (70000, 61872), (70000, 70063), (70000, 78191),
   (70000, 78192), (70000, 200000), (0xffffffffffffe03e, 5), (0xffffffffffffe03f, 5),
   (5, 0xffffffffffffe03d), (5, 0xffffffffffffe03e), (0xffffffffffffe000, 0xffffffffffffe03d),
   (0xffffffffffffe03e, 0xffffffffffffe03d), (0xffffffffffffc000, 0xffffffffffffe03c)]

#eval show IO Unit from do
  let mut runs := 0
  let mut calls := 0
  let mut iterations := 0
  let mut failures : List String := []
  for (counter, nonce) in counterCases do
    for bitmap in [Bitmap.pattern, Bitmap.ones] do
      for (mode, recorded) in [(0, 0), (2, 3), (3, 9), (3, 0)] do
        for (seed, preempt) in [((1 : UInt64), 0x100), (0xfeedfacecafebeef, 0xfffffe00)] do
          runs := runs + 1
          match trace { counter, nonce, bitmap, mode, recorded, preempt } seed with
          | .ok seen =>
            calls := calls + seen.calls
            iterations := iterations + seen.loop
          | .error e => failures := s!"counter {counter} nonce {nonce} mode {mode}: {e}" :: failures
  if failures.isEmpty then
    IO.println s!"C2CutTrace: {runs} runs, {calls} calls, {iterations} loop iterations: every cut predicate held"
  else throw <| IO.userError s!"C2CutTrace: {failures.length} of {runs} runs fail; first: {failures.getLast!}"

end Binary.C2.CutTrace
