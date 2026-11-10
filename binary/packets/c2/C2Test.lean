import C2Statement
import Leanux.Runner

/-! Result C2: executed tests of the final statement (`binary/C2Statement.lean`). Not
proofs, and in no lake target; compiled by `binary/packets/c2/check`.

The committed range terms (all 70, the `bts` included), the two callback entries, and
the landed terms of the PC callback and the comparison body are run with Kraken's
interpreter on constructed states. Each run is compared with the mirror's own
`Leanux.WG.counterValidate` on a world holding the same replay state, through
executable forms of `Refines` and `Kept`. Deliberately wrong variants of the statement,
of the representation and of the `bts` must fail.

Every executed `bts` is also compared with `reference`, the semantics the statement
packet proposed for it before Kraken had the instruction (the packet's placeholder,
kept here as test code only): any difference fails the run. -/
namespace Binary.C2.Test
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-! ### Running the machine -/

/-- Kraken's effect tree, run. The `n`-th undefined value of one instruction (from 1)
is drawn from the seed shifted right by `n`, so the five undefined flags of the `bts`
take bits 1 to 5 of the seed, as the packet's placeholder runs did. -/
partial def effects (seed : UInt64) (cur : MachineState) (n : Nat := 1) : Effects → Except String MachineState
  | .done s => pure s
  | .require_read_access a w k => do
    unless (cur.data.dmem.loadBytes a w.bytes).isSome do throw s!"unmapped read {a}"
    effects seed cur n (k ())
  | .require_write_access a w k => do
    unless (cur.data.dmem.loadBytes a w.bytes).isSome do throw s!"unmapped write {a}"
    effects seed cur n (k ())
  | .require_exec_access _ k => effects seed cur n (k ())
  | @Effects.undefined _ t k => effects seed cur (n + 1) (k (t.from_hash (seed >>> UInt64.ofNat n)))
  | .unimplemented e => throw e
  | .gp_unaligned a _ => throw s!"unaligned access {a}"
  | .nonmem_load _ a _ _ => throw s!"nonmemory load {a}"
  | .nonmem_store _ a _ _ => throw s!"nonmemory store {a}"

def readNat (m : Mem 64) (a n : Nat) : Except String Nat := do
  let some v := m.loadInt (.ofNat 64 a) n | throw s!"unmapped read at {a}"
  return v.toNat

/-- The address of `bts %r15,(%rax)` in the range. -/
def btsPC : Int64 := .ofNat 0xffffffff8139d3dd

/-- How the `bts` is executed: by Kraken's interpreter from the committed term (`real`),
or by a deliberately wrong variant substituted at its address. -/
inductive Bts where
  | real | carryNewBit | noStore | nextWord | bitPlusOne
  deriving BEq

/-- The semantics the statement packet proposed for the `bts` (its placeholder
`btsResult`, verbatim): CF the old bit, the quadword written back with the bit set, the
five other flags as given. Test code: the base of the wrong variants, and the reference
every real `bts` step is compared with. -/
def reference (s : MachineState) (word : BitVec 64) (pf af zf sf of : Bool) : MachineState :=
  let bit := s.data.regs.r15.toNat
  ⟨{ s.data with
      dmem := s.data.dmem.storeInt s.data.regs.rax.toBitVec 8 ((word ||| (1#64 <<< bit)).toNat : Int)
      status := { cf := word.getLsbD bit, pf, af, zf, sf, of } },
    s.pc + 4⟩

def referenceStep (seed : UInt64) (s : MachineState) : Except String (MachineState × BitVec 64) := do
  unless s.data.regs.r15.toNat < 64 do throw "bts: bit offset outside the quadword"
  let some v := s.data.dmem.loadInt s.data.regs.rax.toBitVec 8 | throw "bts: unmapped quadword"
  let word : BitVec 64 := .ofNat 64 v.toNat
  let f (i : Nat) : Bool := (seed >>> UInt64.ofNat i) % 2 == 1
  return (reference s word (f 1) (f 2) (f 3) (f 4) (f 5), word)

/-- A wrong `bts`, substituted for the real one. -/
def btsStep (variant : Bts) (seed : UInt64) (s : MachineState) : Except String MachineState := do
  let (good, word) ← referenceStep seed s
  let f (i : Nat) : Bool := (seed >>> UInt64.ofNat i) % 2 == 1
  match variant with
  | .real => throw "the real bts is not substituted"
  | .carryNewBit => return ⟨{ good.data with status := { good.data.status with cf := true } }, good.pc⟩
  | .noStore => return ⟨{ good.data with dmem := s.data.dmem }, good.pc⟩
  | .nextWord =>
    let other := reference
      ⟨{ s.data with regs := { s.data.regs with rax := s.data.regs.rax + 8 } }, s.pc⟩ word (f 1) (f 2) (f 3) (f 4) (f 5)
    return ⟨{ other.data with regs := s.data.regs }, other.pc⟩
  | .bitPlusOne =>
    let other := reference
      ⟨{ s.data with regs := { s.data.regs with r15 := (s.data.regs.r15 + 1) % 64 } }, s.pc⟩ word (f 1) (f 2) (f 3) (f 4) (f 5)
    return ⟨{ other.data with regs := s.data.regs }, other.pc⟩

/-- The state Kraken's `bts` produced against the packet's proposal for it: PC, every
register, all six flags, the system flags, and the three quadwords around the
destination (the frame over every other mapped byte is checked at the exit). -/
def agrees (seed : UInt64) (s t : MachineState) : Except String Unit := do
  let (want, _) ← referenceStep seed s
  let quad (m : DataMem) (k : Nat) := m.loadInt (s.data.regs.rax.toBitVec + .ofNat 64 (8 * k) - 8) 8
  unless t.pc == want.pc && t.data.regs == want.data.regs && t.data.system == want.data.system &&
      t.data.status.cf == want.data.status.cf && t.data.status.pf == want.data.status.pf &&
      t.data.status.af == want.data.status.af && t.data.status.zf == want.data.status.zf &&
      t.data.status.sf == want.data.status.sf && t.data.status.of == want.data.status.of &&
      (List.range 3).all (fun k => quad t.data.dmem k == quad want.data.dmem k) do
    throw "Kraken's bts differs from the packet's proposed semantics"

/-- The callbacks: the image's own code, or a `ret` that also overwrites every
caller-saved register (what the ABI clause `Returned` permits a callee to do). -/
inductive Callbacks where
  | image | scramble
  deriving BEq

def fetchAll (pc : Int64) : Option Decoded :=
  (Range.fetch pc).orElse fun _ => ServiceImage.fetch pc

/-- Run from `initial` to the first exit PC. Returns the exit state and the number of
instructions executed. -/
def run (callbacks : Callbacks) (bts : Bts) (seed : UInt64) (initial : MachineState) :
    Except String (MachineState × Nat) := do
  let mut s := initial
  for tick in [:60000] do
    if exits.contains s.pc then return (s, tick)
    if s.pc == btsPC && bts != .real then
      s ← btsStep bts seed s
      continue
    if callbacks == .scramble && Range.callees.contains s.pc then
      let ra ← readNat s.data.dmem s.data.regs.rsp.toNat 8
      let junk : UInt64 := seed + 0x9e3779b97f4a7c15 * (UInt64.ofNat tick + 1)
      s := ⟨{ s.data with regs := { s.data.regs with
        rsp := s.data.regs.rsp + 8, rax := junk, rcx := junk + 1, rdx := junk + 2,
        rsi := junk + 3, rdi := junk + 4, r8 := junk + 5, r9 := junk + 6, r10 := junk + 7,
        r11 := junk + 8 } }, .ofNat ra⟩
      continue
    let some i := fetchAll s.pc | throw s!"no instruction at {s.pc}"
    let t ← effects seed s 1 (i.instruction.interp s.data ⟨s.pc, s.pc + .ofNat i.size⟩
      (fun d => .done ⟨d, s.pc + .ofNat i.size⟩) (fun p d => .done ⟨d, p⟩))
    if s.pc == btsPC then agrees seed s t
    s := t
  throw "instruction budget exhausted"

/-! ### Constructed states -/

def sp : Nat := 0x400800
def kp : Nat := 0x700000
def skb : Nat := 0x600000
def task : Nat := 0x500000
def area : Nat := 0x800000
def capacity : Nat := 64
def preemptAddr : Nat := 0xffffffff81cc85c8
def taskAddr : Nat := 0xffffffff81cc85c0
def put (m : DataMem) (a size v : Nat) : DataMem := m.storeInt (.ofNat 64 a) size v

/-- Every mapped region, as (address, quadwords). The comparison of the frame reads all
of them. -/
def regions : List (Nat × Nat) :=
  [(sp - 0x40, 16), (kp, 151), (skb, 8), (task + 0x6c0, 12), (area - 16, capacity + 4),
   (taskAddr, 6)]

/-- The initial replay bitmap: a pattern, all clear, or all set. -/
inductive Bitmap where
  | pattern | zero | ones
def Bitmap.word : Bitmap → Nat → Nat
  | .pattern, j => 0xa5a5000000000000 + 0x0101010101 * (j + 1)
  | .zero, _ => 0
  | .ones, _ => 0xffffffffffffffff

structure Setup where
  counter : Nat
  nonce : Nat
  bitmap : Bitmap := .pattern
  /-- KCOV mode of the current task: 0 off, 2 PCs, 3 comparisons. -/
  mode : Nat := 0
  /-- Records already in the coverage buffer. -/
  recorded : Nat := 0
  preempt : Nat := 0x100
  windowOffset : Nat := 136

def filler (a : Nat) : Nat := 0xc0de000000000000 + a * 0x9e37 % 2^48

def memory (c : Setup) (previous : Option DataMem := none) : DataMem := Id.run do
  let mut m : DataMem := ∅
  for (a, n) in regions do
    for i in [:n] do m := put m (a + 8*i) 8 (filler (a + 8*i))
  m := put m (skb + 0x28) 8 c.nonce
  match previous with
  | some old =>
    for i in [:129] do
      m := put m (kp + c.windowOffset + 8*i) 8 ((old.loadInt (.ofNat 64 (kp + c.windowOffset + 8*i)) 8).getD 0).toNat
  | none =>
    m := put m (kp + c.windowOffset) 8 c.counter
    for j in [:128] do m := put m (kp + c.windowOffset + 8 + 8*j) 8 (c.bitmap.word j)
  m := put m taskAddr 8 task
  m := put m preemptAddr 4 c.preempt
  m := put m (task + 0x6e0) 4 c.mode
  m := put m (task + 0x6e4) 4 capacity
  m := put m (task + 0x6e8) 8 area
  m := put m (task + 0x704) 4 1
  m := put m area 8 c.recorded
  return m

def initial (c : Setup) (previous : Option DataMem := none) : MachineState :=
  let regs : Reg64s := {
    rsp := .ofNat sp, r13 := .ofNat kp, rbx := .ofNat skb, r12 := 0x1234,
    rbp := 0xffffffffffffff77, r14 := 78, r15 := 79, rax := 80 }
  ⟨{ regs := regs, dmem := memory c previous }, Range.entry⟩

/-! ### The mirror -/

def bitmapOf (b : Bitmap) : Array Nat := Array.ofFn (n := 128) fun j => b.word j.val

def worldOf (rc : WG.ReplayCounter) : WGWorld :=
  let k : WG.Keypair := { peer := none, receivingCounter := rc }
  let ks : Std.TreeMap WG.KeypairId WG.Keypair := (∅ : Std.TreeMap WG.KeypairId WG.Keypair).insert 0 k
  let d : WG.Device := { ifindex := 3, ifname := "wg0", keypairs := ks }
  { dev := some d }

def ambient : Ambient := { env := Leanux.Runner.harnessEnv, timing := Leanux.Env.timing }

/-- The mirror's own function on a world holding `rc`: result, and the replay state left. -/
def mirror (rc : WG.ReplayCounter) (nonce : Nat) : Except String (Bool × WG.ReplayCounter) :=
  match ((WG.counterValidate 0 nonce).run (worldOf rc)).run ambient with
  | .error e => .error s!"mirror refused: {e.message}"
  | .ok ((result, world'), _) =>
    match windowOf world' 0 with
    | some rc' => .ok (result, rc')
    | none => .error "mirror lost the keypair"

/-! ### Executable forms of the statement -/

/-- The parts of the statement a wrong variant changes. -/
structure Spec where
  exitPC : WG.ReplayCounter → Nat → Int64 := exitPC
  accepted : MachineState → Bool := accepted
  /-- Offset of the replay state in the keypair, as the representation has it. -/
  windowOffset : Nat := Layouts.keypair_receiving_counter
  wordOffset : Nat → Nat := fun j => Layouts.replay_backtrack + j * Layouts.replayWordBytes
  preemptStep : Nat := 0x200

/-- Read the replay state that `Layouts.ReplayFields` relates to these bytes (the
relation is functional: `ReplayFields.functional`). -/
def represented (spec : Spec) (m : Mem 64) : Except String WG.ReplayCounter := do
  let counter ← readNat m (kp + spec.windowOffset) 8
  let mut words : Array Nat := #[]
  for j in [:128] do words := words.push (← readNat m (kp + spec.windowOffset + spec.wordOffset j) 8)
  return { counter, backtrack := words }

def inFootprint (a : Nat) : Bool :=
  (sp - 8 ≤ a && a < sp) || (sp + 0x10 ≤ a && a < sp + 0x20) ||
  (kp + 136 ≤ a && a < kp + 136 + 1032) || (preemptAddr ≤ a && a < preemptAddr + 4)

/-- `Kept`, executably: the frame over every mapped byte, the preempt count, the
coverage metadata, the registers. -/
def kept (spec : Spec) (c : Setup) (s t : MachineState) : Except String Unit := do
  unless t.data.regs.rsp == s.data.regs.rsp && t.data.regs.rbx == s.data.regs.rbx &&
    t.data.regs.r12 == s.data.regs.r12 && t.data.regs.r13 == s.data.regs.r13 do throw "registers differ"
  unless (← readNat t.data.dmem preemptAddr 4) == (c.preempt + spec.preemptStep) % 2^32 do
    throw "preempt count differs"
  let recording := c.mode == 2 || c.mode == 3
  for (a, n) in regions do
    for i in [:8*n] do
      let b := a + i
      if inFootprint b then continue
      if recording && area ≤ b && b < area + 8 * capacity then continue
      unless (← readNat t.data.dmem b 1) == (← readNat s.data.dmem b 1) do throw s!"byte {b} written"
  let count ← readNat t.data.dmem area 8
  if recording then unless count ≤ capacity do throw "coverage count beyond the capacity"
  -- the metadata half of `Kept.coverage`, read as `KcovMetadata` reads it
  unless (← readNat t.data.dmem taskAddr 8) == task && (← readNat t.data.dmem (task + 0x6e0) 4) == c.mode &&
      (← readNat t.data.dmem (task + 0x6e4) 4) == capacity && (← readNat t.data.dmem (task + 0x6e8) 8) == area &&
      (← readNat t.data.dmem (task + 0x704) 4) == 1 do throw "coverage metadata changed"
  if t.pc == Range.donePC then
    unless t.data.regs.rsi.toNat % 2^32 == 0x200 do throw "%esi is not 0x200 at the last exit"

/-- One visit against `Refines`: exit, acceptance, the represented state, `Kept`. -/
def check (spec : Spec) (callbacks : Callbacks) (bts : Bts) (c : Setup) (seed : UInt64) :
    Except String Bool := do
  let s := initial c
  let before ← represented spec s.data.dmem
  let (result, after) ← mirror before c.nonce
  let (t, _) ← run callbacks bts seed s
  unless t.pc == spec.exitPC before c.nonce do throw "exit differs"
  unless spec.accepted t == result do throw s!"acceptance differs (mirror: {result})"
  let final ← represented spec t.data.dmem
  unless final.counter == after.counter do throw "counter differs from the mirror's"
  for j in [:128] do
    unless final.backtrack[j]! == after.backtrack[j]! do throw s!"bitmap word {j} differs from the mirror's"
  kept spec c s t
  return result

/-- (stored counter, packet counter): fresh, in window, at each edge, too old, far
ahead, at and around the limits. -/
def cases : List (Nat × Nat) :=
  [(0, 0), (100, 50), (100, 99), (100, 110), (100, 127), (100, 200), (100, 100 + 64*200),
   (64*127 + 5, 64*130), (70, 64*129 + 3), (70, 64*128 + 3), (70, 64*130 + 3),
   (0x3000, 0x3000 - 0x1fc1), (0x3000, 0x3000 - 0x1fc2), (0x3000, 0),
   (0xffffffffffffe03e, 0xffffffffffffe030), (0xffffffffffffe03f, 0xffffffffffffe030),
   (0xffffffffffffe000, 0xffffffffffffe03d), (0xffffffffffffe000, 0xffffffffffffe03e),
   (5, 0xffffffffffffffff), (0xffffffffffffffff, 3), (0, 0xffffffffffffe03d), (1, 0), (64, 63),
   (0xffffffffffffe03e, 0xffffffffffffe03d), (8129 + 1, 0), (8129 + 1, 1), (200, 135)]

/-- Callback and coverage settings: (callbacks, mode, records already present). -/
def settings : List (Callbacks × Nat × Nat) :=
  [(.image, 0, 0), (.image, 3, 0), (.image, 3, 9), (.image, 2, 0), (.image, 2, 62), (.scramble, 0, 0)]

def suite (spec : Spec) (bts : Bts) (settings : List (Callbacks × Nat × Nat))
    (bitmaps : List Bitmap) : List String × Nat × Nat := Id.run do
  let mut failures := []
  let mut runs := 0
  let mut acceptedRuns := 0
  for (counter, nonce) in cases do
    for bitmap in bitmaps do
      for (callbacks, mode, recorded) in settings do
        for (seed, preempt) in [((1 : UInt64), 0x100), (0xfeedfacecafebeef, 0xfffffe00)] do
          runs := runs + 1
          let offset := spec.windowOffset
          match check spec callbacks bts { counter, nonce, bitmap, mode, recorded, preempt, windowOffset := offset } seed with
          | .ok true => acceptedRuns := acceptedRuns + 1
          | .ok false => pure ()
          | .error e => failures := failures ++ [s!"({counter},{nonce}) mode {mode}/{recorded} seed {seed}: {e}"]
  return (failures, runs, acceptedRuns)

/-! ### Wrong variants -/

def wrong : List (String × Spec × Bts) :=
  [("statement: counter limit one lower",
      { exitPC := fun c n => if c.counter ≥ WG.REJECT_AFTER_MESSAGES then Range.rejectWindowPC else exitPC c n }, .real),
   ("statement: packet limit strict",
      { exitPC := fun c n => if n = WG.REJECT_AFTER_MESSAGES ∧ c.counter ≤ WG.REJECT_AFTER_MESSAGES
          then Range.donePC else exitPC c n }, .real),
   ("statement: the two rejection exits swapped",
      { exitPC := fun c n => let pc := exitPC c n
          if pc == Range.rejectWindowPC then Range.rejectLimitPC
          else if pc == Range.rejectLimitPC then Range.rejectWindowPC else pc }, .real),
   ("statement: %bpl = 1 read as acceptance",
      { accepted := fun t => t.pc == Range.donePC && t.data.regs.rbp.toNat % 256 == 1 }, .real),
   ("statement: bottom halves re-enabled at the exit", { preemptStep := 0 }, .real),
   ("representation: bitmap word order reversed",
      { wordOffset := fun j => Layouts.replay_backtrack + (127 - j) * Layouts.replayWordBytes }, .real),
   ("representation: bitmap one word later",
      { wordOffset := fun j => Layouts.replay_backtrack + ((j + 1) % 128) * Layouts.replayWordBytes }, .real),
   ("bts: CF is the new bit", {}, .carryNewBit),
   ("bts: the quadword is not written back", {}, .noStore),
   ("bts: the next quadword", {}, .nextWord),
   ("bts: the next bit", {}, .bitPlusOne)]

/-! ### Results: printed, and the compilation fails on any surprise -/

def all : List Bitmap := [.pattern, .zero, .ones]
def reduced : List (Callbacks × Nat × Nat) := [(.image, 3, 9), (.scramble, 0, 0)]

#eval show IO Unit from do
  -- The terms cover the range: 70 instructions, 5 + 5 callback-entry instructions, and
  -- the term at the `bts` address is Kraken's `bts %r15,(%rax)`.
  let bts : Instr := .regular .W64 .W64 (.bts {base := some (.reg .rax), idx := none} (.low .r15 .W64))
  unless Range.code.length == Range.count && Range.count == 70 &&
      Range.cmp8Stub.length == 5 && Range.constCmp8Stub.length == 5 &&
      ((Range.fetch btsPC).map fun i => i.instruction == bts && i.size == 4) == some true do
    throw (IO.userError "the committed terms do not cover the range")
  -- Exit taken, %bpl and instructions executed per case (pattern bitmap, comparisons recorded).
  IO.println (cases.map fun (counter, nonce) =>
    match run .image .real 1 (initial { counter, nonce, mode := 3 }) with
    | .ok (t, n) => s!"{t.pc.toBitVec.toNat - Range.entry.toBitVec.toNat}:{t.data.regs.rbp.toNat % 256}/{n}"
    | .error e => e)
  let (failures, runs, acc) := suite {} .real settings all
  IO.println s!"statement as written: {runs} runs, {acc} accepted, {failures.length} failures"
  unless failures.isEmpty do throw (IO.userError s!"the statement fails: {failures.take 5}")
  unless acc > 0 do throw (IO.userError "no accepting run")
  for (name, spec, bts) in wrong do
    let (failures, runs, _) := suite spec bts reduced [.pattern, .ones]
    IO.println s!"wrong variant, {name}: {failures.length} of {runs} runs fail"
    if failures.isEmpty then throw (IO.userError s!"wrong variant passes: {name}")

end Binary.C2.Test
