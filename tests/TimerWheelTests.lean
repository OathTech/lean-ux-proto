import Leanux.Kernel.TimerWheel

/-!
# The timer wheel's arithmetic and order (B3)

docs/2026-10-15-design-b3-timer-wheel.md, sections 1.4, 3.1 and 3.3: the
levels, widths and late bounds of every WireGuard delay at HZ 250 against
`calc_wheel_index` (kernel/time/timer.c:567-620), the rounding, the lead of
one, the same-slot and move decisions of `__mod_timer`, the pass's order key
(ascending bucket expiry, the highest level first at one step, the newest
enqueue first within a slot) including the equal-expiry case the live corpus
never shows, and the pending-iff-slotted invariant.
Run: `lake build leanux-timer-wheel-tests && .lake/build/bin/leanux-timer-wheel-tests`.
-/

open Leanux Leanux.WG Leanux.TimerWheel

abbrev Check := Except String Unit
def fail (msg : String) : Check := .error msg
def ok : Check := .ok ()
def ensure (cond : Bool) (msg : String) : Check := if cond then ok else fail msg

/-- A base clock well past 2^32, as `jiffies` is after an advance
    (`INITIAL_JIFFIES` = 2^32 - 75000). -/
def J : UInt64 := 4295000000

/-- A bare peer: the four required fields and the defaults. -/
def bare : Peer := { remoteStatic := List.replicate 32 0, presharedKey := List.replicate 32 0,
                     precomputedStaticStatic := List.replicate 32 0, internalId := 1 }

/-- The table of section 1.4: (delay, level, width). -/
def table : List (Nat × Nat × Nat) :=
  [(1250, 2, 64), (1332, 2, 64), (2500, 2, 64), (3750, 2, 64), (3832, 2, 64), (135000, 4, 4096),
   (250, 1, 8), (500, 1, 8), (750, 2, 64), (6250, 3, 512), (7500, 3, 512)]

def levelsAndWidths : List Check :=
  table.map fun (delay, lvl, width) =>
    let e := J + delay.toUInt64
    let (slot, bexp) := calcWheelIndex e J
    ensure (levelOf slot == lvl && LVL_GRAN lvl == width
            && timeAfter bexp e && timeBeforeEq bexp (e + width.toUInt64)
            && (bexp.toNat % width == 0))
      s!"delay {delay}: slot {slot} (level {levelOf slot}, expected {lvl}), bucket expiry {bexp} for expires {e}"

def checks : List (String × Check) :=
  (List.range levelsAndWidths.length).zip levelsAndWidths |>.map (fun (i, c) => (s!"table row {i}", c)) |>.append [
  ("LVL_START thresholds", ensure (LVL_START 1 == 63 && LVL_START 2 == 504 && LVL_START 3 == 4032
      && LVL_START 4 == 32256 && LVL_START 5 == 258048 && LVL_DEPTH == 9 && WHEEL_SIZE == 576) "constants"),
  ("rounding up: a timer fires no earlier than expires + 1",
    ensure ((List.range 70).all fun k =>
      let e := J + 1250 + k.toUInt64
      let (_, bexp) := calcWheelIndex e J
      timeAfter bexp e && timeBeforeEq bexp (e + 64)) "rounding"),
  ("the lead of one: clk = jiffies + 1 after a pass changes no WireGuard level",
    ensure (table.all fun (delay, lvl, _) => levelOf (calcWheelIndex (J + delay.toUInt64) (J + 1)).1 == lvl) "lead"),
  ("the 2 s keepalive moves to level 2 at a lag of 4",
    ensure (levelOf (calcWheelIndex (J + 500) (J - 3)).1 == 1 && levelOf (calcWheelIndex (J + 500) (J - 4)).1 == 2) "lag"),
  ("the keepalive re-arm inside a catch-up pass of 4200 lands on level 3",
    ensure (levelOf (calcWheelIndex (J + 4201 + 2500) (J + 1)).1 == 3) "catch-up"),
  ("the past: an expiry behind the clock takes the current slot",
    ensure (calcWheelIndex (J - 5) J == (J.toNat &&& LVL_MASK, J)) "past"),
  ("same slot: a re-arm within the bucket keeps the entry",
    let p := bare
    let (slot, bexp) := calcWheelIndex (J + 6250) J
    let we : WheelEntry := ⟨slot, bexp, 1⟩
    let p := ((p.setTimer .persistentKeepalive (some (J + 6250))).setWheel .persistentKeepalive (some we))
    match place p .persistentKeepalive (J + 6251) (J + 1) with
    | .kept we' => ensure (we' == we) "kept entry"
    | .enqueued _ _ => fail "a re-arm one tick later in a 512-wide bucket moved"),
  ("move: a re-arm into another bucket re-enqueues",
    let p := bare
    let (slot, bexp) := calcWheelIndex (J + 6250) J
    let p := ((p.setTimer .persistentKeepalive (some (J + 6250))).setWheel .persistentKeepalive (some ⟨slot, bexp, 1⟩))
    match place p .persistentKeepalive (J + 6250 + 512) (J + 512) with
    | .kept _ => fail "a re-arm 512 ticks later kept its slot"
    | .enqueued slot' _ => ensure (slot' != slot) "another slot"),
  ("order: ascending bucket expiry",
    ensure (runsBefore ⟨64, J + 64, 2⟩ ⟨65, J + 128, 1⟩ && !runsBefore ⟨65, J + 128, 1⟩ ⟨64, J + 64, 2⟩) "ascending"),
  ("order at one step: the higher level first",
    ensure (runsBefore ⟨130, J + 512, 1⟩ ⟨66, J + 512, 2⟩ && !runsBefore ⟨66, J + 512, 2⟩ ⟨130, J + 512, 1⟩) "level"),
  ("order within a slot: the newest enqueue first",
    ensure (runsBefore ⟨64, J + 64, 2⟩ ⟨64, J + 64, 1⟩ && !runsBefore ⟨64, J + 64, 1⟩ ⟨64, J + 64, 2⟩) "LIFO"),
  ("the invariant: pending iff slotted",
    let p := bare
    ensure ((peerWheelProblem p).isNone
            && (peerWheelProblem (p.setTimer .sendKeepalive (some J))).isSome
            && (peerWheelProblem (p.setWheel .sendKeepalive (some ⟨64, J, 1⟩))).isSome
            && (peerWheelProblem ((p.setTimer .sendKeepalive (some J)).setWheel .sendKeepalive (some ⟨64, J, 1⟩))).isNone) "invariant")]

def main (_ : List String) : IO UInt32 := do
  let mut failures := 0
  for (name, c) in checks do
    match c with
    | .ok () => pure ()
    | .error msg =>
      IO.println s!"FAIL {name}: {msg}"
      failures := failures + 1
  IO.println s!"timer wheel tests: {checks.length} checks, {failures} failures"
  return if failures == 0 then 0 else 1
