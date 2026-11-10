import C2Test
import Std.Data.HashSet

/-! Result C2, the final statement: a search for states that MEET the premises and
BREAK a conclusion, the `bts` run by Kraken's interpreter. Not a proof, and not
exhaustive.

The first packet's tests built every state from one family of far-apart addresses and
never checked a state against `Context`. An independent review then found a state
meeting the old `Context` on which a packet counter is accepted twice: the coverage
buffer lay over the task's `kcov_area` field (finding H1). Here:

* `contextHolds` decides every field of `Context` numerically on a constructed state,
  in its old form and in the revised one (with `coverageMetadata`);
* states map only the bytes `Context` requires, and are placed adversarially: each
  region the statement mentions is put adjacent to, one byte into, and exactly over
  each other region, over single interesting fields, and across the top of the address
  space; then pairs of such placements;
* every state that passes the check is run, and every conclusion of `Refines` and
  `Kept` is checked on it (exit, acceptance, window against the mirror, registers,
  preempt count, coverage metadata, the frame over every mapped byte), and, as a second
  visit after an accepting one with the same counter, that it refuses;
* the review's counterexample is kept: it must pass the old check, fail the new one,
  and accept counter 63 twice. -/
namespace Binary.C2.Adversarial
open Binary TrustBase Leanux Binary.C2.Test
local instance : Labels := Binary.Image.linkedLabels

def top : Nat := 2 ^ 64

structure Layout where
  sp : Nat := 0x400800
  kp : Nat := 0x700000
  skb : Nat := 0x600000
  task : Nat := 0x500000
  area : Nat := 0x800000
  cap : Nat := 8
  mode : Nat := 2
  count : Nat := 1
  preempt : Nat := 0x100
  softirq : Nat := 1
  /-- Order in which the regions are written when the state is built (they may overlap). -/
  order : Nat := 0

def Layout.recording (l : Layout) : Bool := l.mode == 2 || l.mode == 3

abbrev Span := Nat × Nat   -- base (mod 2^64), length in bytes
def span (base len : Nat) : Span := (base % top, len)
def bytesOf (r : Span) : List Nat := (List.range r.2).map fun i => (r.1 + i) % top
def setOf (rs : List Span) : Std.HashSet Nat := rs.foldl (fun s r => s.insertMany (bytesOf r)) {}
def disjoint (a b : List Span) : Bool :=
  let s := setOf a
  b.all fun r => (bytesOf r).all fun x => !s.contains x

def Layout.window (l : Layout) : Span := span (l.kp + 136) 1032
def Layout.stack (l : Layout) : List Span := [span (l.sp + top - 8) 8, span (l.sp + 0x10) 16]
def preemptSpan : Span := span preemptAddr 4
def Layout.footprint (l : Layout) : List Span := l.stack ++ [l.window, preemptSpan]
def Layout.metadata (l : Layout) : List Span :=
  [span taskAddr 8, span (l.task + 0x6e0) 4, span (l.task + 0x6e4) 4, span (l.task + 0x6e8) 8,
   span (l.task + 0x704) 4]
def Layout.storage (l : Layout) : List Span := [span l.area 8, span l.area (8 * l.cap)]
def Layout.nonceSlot (l : Layout) : Span := span (l.skb + 0x28) 8

/-- Build a state mapping only what `Context` requires. Regions may overlap; the later
write wins, and `contextHolds` then says whether the result still meets the premises. -/
def build (l : Layout) (counter nonce : Nat) (words : Nat → Nat) : MachineState := Id.run do
  let buffer (m : DataMem) : DataMem := Id.run do
    let mut m := m
    if l.recording then
      for w in [:l.cap] do m := put m (l.area + 8*w) 8 (filler (l.area + 8*w))
      m := put m l.area 8 l.count
    return m
  let window (m : DataMem) : DataMem := Id.run do
    let mut m := put m (l.kp + 136) 8 counter
    for j in [:128] do m := put m (l.kp + 144 + 8*j) 8 (words j)
    return m
  let stack (m : DataMem) : DataMem :=
    put (put (put m (l.sp + top - 8) 8 0xdead0001) (l.sp + 0x10) 8 0xdead0002) (l.sp + 0x18) 8 0xdead0003
  let packet (m : DataMem) : DataMem := put m (l.skb + 0x28) 8 nonce
  let metadata (m : DataMem) : DataMem :=
    put (put (put (put (put (put m taskAddr 8 l.task) preemptAddr 4 l.preempt) (l.task + 0x6e0) 4 l.mode)
      (l.task + 0x6e4) 4 l.cap) (l.task + 0x6e8) 8 l.area) (l.task + 0x704) 4 l.softirq
  let steps := [buffer, window, stack, packet, metadata]
  let steps := match l.order % 3 with
    | 0 => steps
    | 1 => steps.reverse
    | _ => [metadata, buffer, packet, stack, window]
  let m := steps.foldl (fun m f => f m) (∅ : DataMem)
  let regs : Reg64s := {
    rsp := .ofNat (l.sp % top), r13 := .ofNat (l.kp % top), rbx := .ofNat (l.skb % top), r12 := 0x1234,
    rbp := 0xffffffffffffff77, r14 := 78, r15 := 79, rax := 80 }
  return ⟨{ regs := regs, dmem := m }, Range.entry⟩

def mappedSpans (l : Layout) : List Span :=
  l.footprint ++ l.metadata ++ [l.nonceSlot] ++ (if l.recording then l.storage else [])

def loadEq (m : Mem 64) (a n v : Nat) : Bool := (m.loadInt (.ofNat 64 a) n).map (·.toNat) == some v
def mappedAll (m : Mem 64) (rs : List Span) : Bool :=
  rs.all fun r => (bytesOf r).all fun a => (m.get? (.ofNat 64 a)).isSome

/-- Every field of `Context layout preempt s kp skb nonce`, decided on this state, with
`nonce` the quadword the state holds at `skb + 0x28`. Returns (the first packet's
`Context`, the revised `Context`). -/
def contextHolds (l : Layout) (s : MachineState) : Bool × Bool :=
  let m := s.data.dmem
  let coverage := loadEq m taskAddr 8 (l.task % top) && loadEq m (l.task + 0x6e0) 4 l.mode &&
    loadEq m (l.task + 0x6e4) 4 l.cap && loadEq m (l.task + 0x6e8) 8 (l.area % top) &&
    loadEq m (l.task + 0x704) 4 l.softirq && loadEq m preemptAddr 4 l.preempt &&
    (!l.recording ||
      ((List.range l.cap).all (fun w => (m.loadInt (.ofNat 64 (l.area + 8*w)) 8).isSome) &&
        match m.loadInt (.ofNat 64 l.area) 8 with
        | some count => count.toNat ≤ l.cap
        | none => false))
  let old := s.pc == Range.entry && s.data.regs.r13.toNat == l.kp % top && s.data.regs.rbx.toNat == l.skb % top &&
    (m.loadInt (.ofNat 64 (l.skb + 0x28)) 8).isSome &&        -- nonce
    mappedAll m [l.window] &&                                   -- window
    l.sp % 8 == 0 &&                                            -- aligned
    mappedAll m l.stack &&                                      -- stack
    coverage &&                                                 -- coverage
    disjoint l.stack [l.window] &&                              -- stackWindow
    disjoint l.stack [preemptSpan] &&                           -- stackPreempt
    disjoint [l.window] [preemptSpan] &&                        -- windowPreempt
    disjoint (l.metadata ++ (if l.recording then l.storage else [])) l.footprint  -- coverageApart
  (old, old && (!l.recording || disjoint l.storage l.metadata))  -- + coverageMetadata

def windowAt (l : Layout) (m : Mem 64) : Except String WG.ReplayCounter := do
  let counter ← readNat m ((l.kp + 136) % top) 8
  let mut words : Array Nat := #[]
  for j in [:128] do words := words.push (← readNat m ((l.kp + 144 + 8*j) % top) 8)
  return { counter, backtrack := words }

/-- Every conclusion of `Refines` and `Kept` on one run; `none` when all hold. -/
def broken (l : Layout) (s : MachineState) : Option String :=
  let outcome : Except String Unit := do
    let nonce ← readNat s.data.dmem ((l.skb + 0x28) % top) 8
    let before ← windowAt l s.data.dmem
    let (result, after) ← mirror before nonce
    let (t, _) ← run .image .real 1 s
    unless t.pc == exitPC before nonce do throw "exit differs"
    unless accepted t == result do throw s!"acceptance differs (mirror: {result})"
    let final ← windowAt l t.data.dmem
    unless final.counter == after.counter && final.backtrack == after.backtrack do throw "window differs from the mirror's"
    unless t.data.regs.rsp == s.data.regs.rsp && t.data.regs.rbx == s.data.regs.rbx &&
      t.data.regs.r12 == s.data.regs.r12 && t.data.regs.r13 == s.data.regs.r13 do throw "registers differ"
    if t.pc == Range.donePC then unless t.data.regs.rsi.toNat % 2^32 == 0x200 do throw "%esi differs"
    let m := t.data.dmem
    unless loadEq m preemptAddr 4 ((l.preempt + 0x200) % 2^32) do throw "preempt count differs"
    unless loadEq m taskAddr 8 (l.task % top) && loadEq m (l.task + 0x6e0) 4 l.mode &&
      loadEq m (l.task + 0x6e4) 4 l.cap && loadEq m (l.task + 0x6e8) 8 (l.area % top) &&
      loadEq m (l.task + 0x704) 4 l.softirq do throw "coverage metadata changed"
    if l.recording then
      match m.loadInt (.ofNat 64 l.area) 8 with
      | some count => unless count.toNat ≤ l.cap do throw "coverage count beyond the capacity"
      | none => throw "coverage header unmapped"
    let written := setOf (l.footprint ++ (if l.recording then l.storage else []))
    for r in mappedSpans l do
      for a in bytesOf r do
        unless written.contains a || m.get? (.ofNat 64 a) == s.data.dmem.get? (.ofNat 64 a) do
          throw s!"byte {a} outside the footprint written"
  match outcome with
  | .ok () => none
  | .error e => some e

/-- The replay shape: an accepting visit with coverage off, then a visit in layout `l`
with the same counter on the retained window. `some true` = the second visit accepted
(the property is broken); `none` = the pair does not meet the premises. -/
def replayAccepted (l : Layout) (old : Bool) : Option Bool := do
  let first : Layout := { l with mode := 0, order := 0 }
  let s1 := build first 0 63 (fun _ => 0)
  let ok1 := contextHolds first s1
  guard (if old then ok1.1 else ok1.2)
  let (t1, _) ← (run .image .real 1 s1).toOption
  guard (accepted t1)
  let w ← (windowAt l t1.data.dmem).toOption
  let s2 := build l w.counter 63 (fun j => w.backtrack[j]!)
  let ok2 := contextHolds l s2
  guard (if old then ok2.1 else ok2.2)
  guard ((bytesOf l.window).all fun a => s2.data.dmem.get? (.ofNat 64 a) == t1.data.dmem.get? (.ofNat 64 a))
  guard (loadEq s2.data.dmem ((l.skb + 0x28) % top) 8 63 && loadEq s1.data.dmem ((l.skb + 0x28) % top) 8 63)
  match run .image .real 1 s2 with
  | .ok (t2, _) => some (accepted t2)
  | .error _ => some true

/-! ### Placements -/

inductive Param where
  | sp | kp | skb | task | area
  deriving BEq, Repr, Inhabited

def Layout.set (l : Layout) : Param → Nat → Layout
  | .sp, v => { l with sp := v % top }
  | .kp, v => { l with kp := v % top }
  | .skb, v => { l with skb := v % top }
  | .task, v => { l with task := v % top }
  | .area, v => { l with area := v % top }

/-- Parts of each movable object: (offset from its base, length). -/
def handles (cap : Nat) : Param → List (Nat × Nat)
  | .sp => [(top - 8, 8), (0x10, 16)]
  | .kp => [(136, 1032), (136, 8), (144, 8), (152, 8), (136 + 1024, 8)]
  | .skb => [(0x28, 8)]
  | .task => [(0x6e0, 4), (0x6e4, 4), (0x6e8, 8), (0x704, 4)]
  | .area => [(0, 8), (8, 8), (16, 8), (8 * (cap - 1), 8), (0, 8 * cap)]

/-- Places to put them: every region of the base layout, with its owner, and three
fixed targets (a return address inside the range, as in the review's counterexample;
the top of the address space; address zero). -/
def targets (l : Layout) : List (Option Param × Span) :=
  [(some .kp, l.window), (some .kp, span (l.kp + 136) 8), (some .kp, span (l.kp + 152) 8),
   (some .sp, span (l.sp + top - 8) 8), (some .sp, span (l.sp + 0x10) 16),
   (none, preemptSpan), (none, span taskAddr 8),
   (some .task, span (l.task + 0x6e0) 4), (some .task, span (l.task + 0x6e4) 4),
   (some .task, span (l.task + 0x6e8) 8), (some .task, span (l.task + 0x704) 4),
   (some .area, span l.area 8), (some .area, span l.area (8 * l.cap)),
   (some .skb, l.nonceSlot),
   (none, span 0xffffffff8139d2dc 8), (none, span (top - 8) 16), (none, span 0 8)]

/-- Each handle adjacent before and after each target, one byte into it from either
side, and aligned with its start and with its end. -/
def moves (l : Layout) : List (Param × Nat) := Id.run do
  let mut out := []
  for p in [Param.sp, .kp, .skb, .task, .area] do
    for (off, len) in handles l.cap p do
      for (owner, (tb, tl)) in targets l do
        if owner == some p then continue
        for start in [tb + top - len, tb + tl, tb + top - len + 1, tb + tl - 1, tb, tb + tl + top - len] do
          let base := (start + top - off % top) % top
          unless out.contains (p, base) do out := (p, base) :: out
  return out.reverse

structure Tally where
  layouts : Nat := 0
  meetOld : Nat := 0
  meetNew : Nat := 0
  brokenOldOnly : Nat := 0
  brokenNew : Nat := 0
  replayOld : Nat := 0
  replayNew : Nat := 0
  examples : List String := []

def describe (l : Layout) : String :=
  s!"sp={l.sp} kp={l.kp} skb={l.skb} task={l.task} area={l.area} cap={l.cap} mode={l.mode} count={l.count} order={l.order}"

/-- One layout, one (stored counter, packet counter): check, run, tally. -/
def visit (tally : Tally) (l : Layout) (counter nonce : Nat) (words : Nat → Nat) : Tally := Id.run do
  let s := build l counter nonce words
  let (old, new) := contextHolds l s
  let mut t := { tally with layouts := tally.layouts + 1 }
  unless old do return t
  t := { t with meetOld := t.meetOld + 1, meetNew := t.meetNew + (if new then 1 else 0) }
  if let some why := broken l s then
    if new then
      t := { t with brokenNew := t.brokenNew + 1, examples := t.examples ++ [s!"NEW premises: {why}: {describe l}"] }
    else
      t := { t with brokenOldOnly := t.brokenOldOnly + 1 }
      if t.brokenOldOnly ≤ 3 then t := { t with examples := t.examples ++ [s!"old premises only: {why}: {describe l}"] }
  return t

def replay (tally : Tally) (l : Layout) : Tally := Id.run do
  let mut t := tally
  if replayAccepted l true == some true then t := { t with replayOld := t.replayOld + 1 }
  if replayAccepted l false == some true then
    t := { t with replayNew := t.replayNew + 1, examples := t.examples ++ [s!"NEW premises, replay accepted: {describe l}"] }
  return t

def pattern (j : Nat) : Nat := Bitmap.word .pattern j

/-- The settings each placement is tried in: (mode, records present, order, stored
counter, packet counter). Capacity 8 throughout, so buffers fill within a visit. -/
def settings : List (Nat × Nat × Nat × Nat × Nat) :=
  [(2, 1, 0, 0, 63), (2, 7, 0, 0, 63), (3, 0, 0, 0, 63), (3, 1, 0, 100, 200), (0, 0, 0, 0, 63),
   (2, 1, 1, 100, 200), (3, 1, 2, 100, 50), (2, 0, 2, 0, 63)]

def base : Layout := {}

def tryLayout (tally : Tally) (l : Layout) (withReplay : Bool) : Tally := Id.run do
  let mut t := tally
  for (mode, count, order, counter, nonce) in settings do
    t := visit t { l with mode, count, order } counter nonce pattern
  if withReplay then
    t := replay t { l with mode := 2, count := 1 }
    t := replay t { l with mode := 3, count := 0 }
  return t

/-- The review's counterexample (finding H1), in this builder. -/
def reviewLayout : Layout :=
  { kp := 0xffffffff8139d2dc - 152, task := 0x500000, area := 0x500000 + 0x6d8, cap := 8, mode := 2,
    count := 1, preempt := 0 }

#eval show IO Unit from do
  -- 1. The review's counterexample: meets the old `Context`, not the revised one, and
  --    accepts packet counter 63 on both visits.
  let s := build reviewLayout 0 63 (fun _ => 0)
  let (old, new) := contextHolds reviewLayout s
  let twice := replayAccepted reviewLayout true
  IO.println s!"review counterexample: meets old Context {old}, meets revised Context {new}, second visit accepts the same counter: {twice}"
  unless old && !new && twice == some true && replayAccepted reviewLayout false == none do
    throw (IO.userError "the review's counterexample does not behave as recorded")
  -- 2. The first packet's own family of states does meet both forms.
  let plain := contextHolds base (build base 0 63 pattern)
  unless plain == (true, true) do throw (IO.userError "the base layout fails Context")
  -- 3. Single placements.
  let singles := moves base
  let mut t : Tally := {}
  for (p, v) in singles do
    t := tryLayout t (base.set p v) true
  IO.println s!"single placements: {singles.length} layouts, {t.layouts} states built; {t.meetOld} meet the old Context, {t.meetNew} the revised; conclusions broken on {t.brokenOldOnly} meeting only the old and on {t.brokenNew} meeting the revised; replay accepted on {t.replayOld} (old) and {t.replayNew} (revised)"
  -- 4. Pairs of placements of different objects, sampled.
  let arr := singles.toArray
  let mut x := 12345
  let mut pairs := 0
  let mut u : Tally := {}
  for _ in [:1200] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 2^64
    let (p, v) := arr[(x / 2^20) % arr.size]!
    x := (x * 6364136223846793005 + 1442695040888963407) % 2^64
    let (q, w) := arr[(x / 2^20) % arr.size]!
    if p == q then continue
    pairs := pairs + 1
    let l := (base.set p v).set q w
    for (mode, count, order, counter, nonce) in settings.take 4 do
      u := visit u { l with mode, count, order, preempt := 0xfffffe00 } counter nonce pattern
    if pairs % 4 == 0 then u := replay u { l with mode := 2, count := 1 }
  IO.println s!"pairs of placements: {pairs} layouts, {u.layouts} states built; {u.meetOld} meet the old Context, {u.meetNew} the revised; conclusions broken on {u.brokenOldOnly} meeting only the old and on {u.brokenNew} meeting the revised; replay accepted on {u.replayOld} (old) and {u.replayNew} (revised)"
  for line in t.examples ++ u.examples do IO.println s!"  {line}"
  if t.brokenNew + u.brokenNew + t.replayNew + u.replayNew > 0 then
    throw (IO.userError "a state meeting the revised Context breaks a conclusion")
  -- 5. The single placements again at other capacities (the reviewer's follow-up:
  --    capacity 8 fills within a visit, but is one capacity). Capacity 8 is run 3 above.
  let mut total : Tally := {}
  for cap in [0, 1, 2, 3, 40] do
    let b : Layout := { cap }
    let placements := moves b
    let mut c : Tally := {}
    for (p, v) in placements do
      c := tryLayout c (b.set p v) true
    IO.println s!"capacity {cap}: {placements.length} layouts, {c.layouts} states built; {c.meetOld} meet the old Context, {c.meetNew} the revised; conclusions broken on {c.brokenOldOnly} meeting only the old and on {c.brokenNew} meeting the revised; replay accepted on {c.replayOld} (old) and {c.replayNew} (revised)"
    for line in c.examples.filter (·.startsWith "NEW") do IO.println s!"  {line}"
    total := { total with
      layouts := total.layouts + c.layouts, meetOld := total.meetOld + c.meetOld,
      meetNew := total.meetNew + c.meetNew, brokenOldOnly := total.brokenOldOnly + c.brokenOldOnly,
      brokenNew := total.brokenNew + c.brokenNew, replayOld := total.replayOld + c.replayOld,
      replayNew := total.replayNew + c.replayNew }
  IO.println s!"capacities 0, 1, 2, 3, 40 together: {total.layouts} states built; {total.meetOld} meet the old Context, {total.meetNew} the revised; conclusions broken on {total.brokenOldOnly} meeting only the old and on {total.brokenNew} meeting the revised; replay accepted on {total.replayOld} (old) and {total.replayNew} (revised)"
  if total.brokenNew + total.replayNew > 0 then
    throw (IO.userError "a state meeting the revised Context breaks a conclusion at another capacity")
  if t.brokenOldOnly + u.brokenOldOnly == 0 then
    throw (IO.userError "the search did not rediscover the missing separation on its own")

end Binary.C2.Adversarial
