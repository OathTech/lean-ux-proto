import C2Statement
import CallbackCmp8Rule
import CallHistory
import RegionExecution

/-! Result C2, the cut of the proof: the vocabulary the work packages share.

Definitions only. Nothing here is trust surface: the headline (`C2Statement`) mentions
none of it. It fixes, in Lean,

* the window at machine width (`Window`, `WindowAt`) and the function the range
  computes on it (`validate`), which is the pivot between the execution packages and
  the representation package;
* the invariant carried between instructions of the range, across the thirteen call
  sites and around the clear loop (`Carried`);
* the cut points of the range and what holds at each (`AtAdvance`, `AtLoop`, `AtStore`,
  `AtTail`, `AtExit`).

The interface propositions over this vocabulary are in `C2CutInterfaces`; the assembly
of the headline's clauses from them is in `C2CutAssembly`. Provers do not edit these
three files: a needed change is a report to the coordinator. -/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-! ## The window at machine width -/

/-- Where `struct noise_replay_counter` is, in the form the statement writes it. -/
abbrev windowBase (kp : BitVec 64) : BitVec 64 :=
  kp + .ofNat 64 Layouts.keypair_receiving_counter

/-- The replay state as the machine holds it: the counter and the bitmap words. Only
the words below 128 are meant. -/
structure Window where
  counter : BitVec 64
  words : Nat → BitVec 64

/-- The window bytes at `base` hold `w`. The addresses are written as
`Layouts.ReplayFields` writes them. -/
def WindowAt (m : Mem 64) (base : BitVec 64) (w : Window) : Prop :=
  m.loadInt (base + .ofNat 64 Layouts.replay_counter) 8 = some (w.counter.toNat : Int) ∧
  ∀ i, i < Layouts.replayWords →
    m.loadInt (base + .ofNat 64 (Layouts.replay_backtrack + i * Layouts.replayWordBytes))
      Layouts.replayWordBytes = some ((w.words i).toNat : Int)

/-- The mirror's replay state a machine window stands for. -/
def toCounter (w : Window) : WG.ReplayCounter :=
  { counter := w.counter.toNat
    backtrack := Array.ofFn (n := Layouts.replayWords) fun j => (w.words j.val).toNat }

/-- The machine window of a mirror replay state (faithful when the state fits:
`Fits`). -/
def ofCounter (c : WG.ReplayCounter) : Window :=
  { counter := .ofNat 64 c.counter
    words := fun j => .ofNat 64 (c.backtrack.getD j 0) }

/-- A mirror replay state that a machine window can hold. -/
structure Fits (c : WG.ReplayCounter) : Prop where
  counter : c.counter < 2 ^ 64
  size : c.backtrack.size = Layouts.replayWords
  words : ∀ i (h : i < c.backtrack.size), c.backtrack[i] < 2 ^ 64

/-! ## What the range computes

The tests and the arithmetic are the machine's own: the comparisons are unsigned 64-bit
comparisons on the values the instructions compare, and sums wrap. -/

/-- `REJECT_AFTER_MESSAGES`, the immediate of the first comparison. -/
def limit : BitVec 64 := 0xffffffffffffe03e

/-- The word index of the stored counter (`shr $0x6,%r14` at +177). -/
def cur (w : Window) : BitVec 64 := w.counter >>> 6

/-- The number of words the clear loop zeroes (`sub`, `cmp`, `cmova` at +194..+203):
the distance between the two word indices, capped at 128. -/
def top (w : Window) (t : BitVec 64) : Nat := min ((t >>> 6) - cur w).toNat 128

/-- The bitmap after `n` iterations of the clear loop: iteration `i` (from 1) zeroes
word `(cur + i) & 127` (`lea`, `and $0x7f`, `movq $0x0` at +224..+241). -/
def clearWords (words : Nat → BitVec 64) (current : BitVec 64) : Nat → Nat → BitVec 64
  | 0 => words
  | n + 1 => fun j =>
    if j = ((current + BitVec.ofNat 64 (n + 1)) &&& 127).toNat then 0
    else clearWords words current n j

/-- The window after `n` iterations of the clear loop; the counter is not yet stored. -/
def cleared (w : Window) (n : Nat) : Window :=
  { w with words := clearWords w.words (cur w) n }

/-- The window after the advance path: the words cleared, the counter stored (+273). -/
def advance (w : Window) (t : BitVec 64) : Window :=
  { counter := t, words := clearWords w.words (cur w) (top w t) }

/-- The bit `bts` tests: bit `t & 63` of word `(t >> 6) & 127`. -/
def seen (w : Window) (t : BitVec 64) : Bool :=
  (w.words ((t >>> 6) &&& 127).toNat).getLsbD (t &&& 63).toNat

/-- The window after `bts`. -/
def setBit (w : Window) (t : BitVec 64) : Window :=
  { w with words := fun j =>
      if j = ((t >>> 6) &&& 127).toNat then w.words j ||| (1#64 <<< (t &&& 63).toNat)
      else w.words j }

/-- The three rejection tests, in the image's order (+36, +69, +114). -/
def Rejects (w : Window) (nonce : BitVec 64) : Prop :=
  limit < w.counter ∨ limit ≤ nonce ∨ nonce + 0x1fc1 < w.counter

instance (w : Window) (nonce : BitVec 64) : Decidable (Rejects w nonce) := by
  unfold Rejects; infer_instance

/-- What one execution of the range leaves: the exit, the observation, the window. -/
structure Outcome where
  exit : Int64
  accepted : Bool
  window : Window

/-- The outcome of the test-and-set tail on window `w` for incremented counter `t`. -/
def tested (w : Window) (t : BitVec 64) : Outcome :=
  ⟨Range.donePC, !seen w t, setBit w t⟩

/-- THE PIVOT. The range as a function of the window and the packet counter. -/
def validate (w : Window) (nonce : BitVec 64) : Outcome :=
  if limit < w.counter then ⟨Range.rejectWindowPC, false, w⟩
  else if limit ≤ nonce then ⟨Range.rejectLimitPC, false, w⟩
  else if nonce + 0x1fc1 < w.counter then ⟨Range.rejectWindowPC, false, w⟩
  else if w.counter < nonce + 1 then tested (advance w (nonce + 1)) (nonce + 1)
  else tested w (nonce + 1)

/-! ## The carried invariant -/

/-- What holds of the machine at every point of the range from +14 on (after the load
of the packet counter and the add to the preempt count), in particular before and after
each of the thirteen calls and at the head of each loop iteration. `s0` is the entry
state, `w` the window in progress.

* coverage readiness: the callbacks' state is valid for the raised preempt count;
* the window bytes hold `w`;
* the three stack slots the range uses stay mapped;
* nothing outside the footprint and the coverage buffer has changed since entry;
* the stack pointer and the three registers the caller relies on are the entry's.

With the address-only premises of `Context` at `s0` this gives, at each call, the
callback's readiness and the frame of everything else (`CallSite`). The two spill
slots' values and the registers live across calls are path state: the cut predicates
below carry them. -/
structure Carried (layout : KcovLayout) (preempt : BitVec 32) (kp : BitVec 64)
    (s0 : MachineState) (w : Window) (d : MachineData) : Prop where
  coverage : KcovState layout (preempt + 0x200) d.dmem
  window : WindowAt d.dmem (windowBase kp) w
  stack : ∀ a, stackBytes s0.data.regs.rsp.toBitVec a → (d.dmem.get? a).isSome = true
  frame : EqualOutside
    (fun a => Footprint s0.data.regs.rsp.toBitVec kp a ∨
      ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout a))
    s0.data.dmem d.dmem
  rsp : d.regs.rsp = s0.data.regs.rsp
  rbx : d.regs.rbx = s0.data.regs.rbx
  r12 : d.regs.r12 = s0.data.regs.r12
  r13 : d.regs.r13 = s0.data.regs.r13

/-- The spill slot `0x10(%rsp)`: the incremented packet counter. -/
def Slot10 (s0 : MachineState) (d : MachineData) (t : BitVec 64) : Prop :=
  d.dmem.loadInt (s0.data.regs.rsp.toBitVec + 0x10) 8 = some (t.toNat : Int)

/-- The spill slot `0x18(%rsp)`: its word index. -/
def Slot18 (s0 : MachineState) (d : MachineData) (t : BitVec 64) : Prop :=
  d.dmem.loadInt (s0.data.regs.rsp.toBitVec + 0x18) 8 = some ((t >>> 6).toNat : Int)

/-- No state so far is at an exit (the current one included: used at cut points, which
are not exits). -/
def Quiet (e : Executed) : Prop := ∀ u ∈ e.history, u.pc ∉ exits

/-! ## Cut points -/

/-- +161 (`0xffffffff8139d347`), call site 8: the first instruction of the advance path. -/
def advancePC : Int64 := Range.entry + 161
/-- +219 (`0xffffffff8139d381`), call site 10: the head of the clear loop. -/
def loopPC : Int64 := Range.entry + 219
/-- +263 (`0xffffffff8139d3ad`), call site 12: after the clear loop. -/
def storePC : Int64 := Range.entry + 263
/-- +280 (`0xffffffff8139d3be`), call site 13: the test-and-set tail. -/
def tailPC : Int64 := Range.entry + 280

/-- At +161, having passed the three rejection tests with the stored counter below the
incremented packet counter `t`. -/
structure AtAdvance (layout : KcovLayout) (preempt : BitVec 32) (kp : BitVec 64)
    (s0 : MachineState) (w : Window) (t : BitVec 64) (e : Executed) : Prop where
  pc : e.machine.pc = advancePC
  carried : Carried layout preempt kp s0 w e.machine.data
  quiet : Quiet e
  counter : e.machine.data.regs.rbp.toBitVec = w.counter
  index : e.machine.data.regs.r15.toBitVec = t >>> 6
  next : Slot10 s0 e.machine.data t

/-- THE LOOP INVARIANT. At the head of the clear loop with `i` iterations done and at
least one to go: the first `i` words are cleared, `%r14` is the stored counter's word
index, `%rbp` the number of the iteration about to run, `%r15` the iteration count. -/
structure AtLoop (layout : KcovLayout) (preempt : BitVec 32) (kp : BitVec 64)
    (s0 : MachineState) (w : Window) (t : BitVec 64) (i : Nat) (e : Executed) : Prop where
  pc : e.machine.pc = loopPC
  carried : Carried layout preempt kp s0 (cleared w i) e.machine.data
  quiet : Quiet e
  bound : i < top w t
  current : e.machine.data.regs.r14.toBitVec = cur w
  count : e.machine.data.regs.rbp.toBitVec = .ofNat 64 (i + 1)
  iterations : e.machine.data.regs.r15.toBitVec = .ofNat 64 (top w t)
  next : Slot10 s0 e.machine.data t
  index : Slot18 s0 e.machine.data t

/-- At +263: every word of the slide is cleared; the counter is not yet stored. -/
structure AtStore (layout : KcovLayout) (preempt : BitVec 32) (kp : BitVec 64)
    (s0 : MachineState) (w : Window) (t : BitVec 64) (e : Executed) : Prop where
  pc : e.machine.pc = storePC
  carried : Carried layout preempt kp s0 (cleared w (top w t)) e.machine.data
  quiet : Quiet e
  next : Slot10 s0 e.machine.data t
  index : Slot18 s0 e.machine.data t

/-- At +280 with the window `w` prepared for the test-and-set of `t`. -/
structure AtTail (layout : KcovLayout) (preempt : BitVec 32) (kp : BitVec 64)
    (s0 : MachineState) (w : Window) (t : BitVec 64) (e : Executed) : Prop where
  pc : e.machine.pc = tailPC
  carried : Carried layout preempt kp s0 w e.machine.data
  quiet : Quiet e
  next : Slot10 s0 e.machine.data t
  index : Slot18 s0 e.machine.data t

/-- At an exit, as the first one, with outcome `o`. -/
structure AtExit (layout : KcovLayout) (preempt : BitVec 32) (kp : BitVec 64)
    (s0 : MachineState) (o : Outcome) (e : Executed) : Prop where
  pc : e.machine.pc = o.exit
  first : ∀ u ∈ e.history.dropLast, u.pc ∉ exits
  accepted : accepted e.machine = o.accepted
  carried : Carried layout preempt kp s0 o.window e.machine.data
  unlockArgument : e.machine.pc = Range.donePC → e.machine.data.regs.rsi.toNat % 2 ^ 32 = 0x200

/-! ## Regions of the range -/

/-- The address of instruction number `first` of the range (from 0). -/
def regionPC (first : Nat) : Int64 :=
  Range.entry + .ofNat ((Range.code.take first).map (·.size)).sum

/-- `count` consecutive instructions of the range, from number `first`. -/
def regionCode (first count : Nat) : List (Kraken.Sized Directive) :=
  (Range.code.drop first).take count

end Binary.C2
