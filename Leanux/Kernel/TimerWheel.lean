import Leanux.Kernel.Defs

/-!
# kernel/time/timer.c — the timer wheel, restricted to the armed set (B3)

docs/2026-10-15-design-b3-timer-wheel.md (U1, U5 [USER 2026-10-15]). The
wheel's arithmetic (`calc_index`, `calc_wheel_index`, timer.c:567-620) on
the C's `unsigned long`, the placement decision of `__mod_timer` (:1065-1190:
same slot, position kept; else re-enqueued at the head), and the pass's
selection (`__run_timers`, :2390-2422, with `collect_expired_timers`,
:1854-1878, and `expire_timers`, :1813-1852): the earliest pending bucket,
the highest collected level first at one step, the newest enqueue first
within a slot. The per-timer data (`WheelEntry`: the slot stored in the
timer's `flags`, the bucket expiry the enqueue computed, the enqueue stamp)
lives with the peer's timers (`Leanux/WG/Types.lean`); the base's clock and
stamp counter are `Kernel.timerClk` and `Kernel.timerEnqueues`. The record
consumption (kinds 313 and 314) is `WG.armTimer`'s (`Leanux/WG/State.lean`);
the pass itself, which runs the callbacks' sections, is `Env.runTimers`.

The constants are the pinned configuration's: `CONFIG_HZ=250`, so
`LVL_DEPTH 9` (`:175`); one base (`NR_BASES 1`, no `CONFIG_NO_HZ_COMMON`,
`:200`), and every WireGuard timer is in `timer_bases[0]`. `timer.c` is
mirrored but unanchored (U3): its comparisons are checked by the kind-314
record, not by branch witnesses, so they are plain Lean here.
-/

namespace Leanux.TimerWheel
open Leanux Leanux.WG

/-- `LVL_CLK_SHIFT` (timer.c:154): each level is 8 times coarser. -/
def LVL_CLK_SHIFT : Nat := 3
def LVL_CLK_DIV : Nat := 1 <<< LVL_CLK_SHIFT
def LVL_CLK_MASK : Nat := LVL_CLK_DIV - 1
def LVL_SHIFT (n : Nat) : Nat := n * LVL_CLK_SHIFT
/-- `LVL_GRAN(n)` (:158): a level-`n` bucket is `8^n` ticks wide. -/
def LVL_GRAN (n : Nat) : Nat := 1 <<< LVL_SHIFT n
/-- `LVL_BITS` 6 (:168): 64 slots per level. -/
def LVL_BITS : Nat := 6
def LVL_SIZE : Nat := 1 <<< LVL_BITS
def LVL_MASK : Nat := LVL_SIZE - 1
def LVL_OFFS (n : Nat) : Nat := n * LVL_SIZE
/-- `LVL_START(n) = (LVL_SIZE - 1) << ((n - 1) * LVL_CLK_SHIFT)` (:165): the
    first delta of level `n` (63, 504, 4032, 32256, 258048, …). -/
def LVL_START (n : Nat) : UInt64 := ((LVL_SIZE - 1) <<< ((n - 1) * LVL_CLK_SHIFT)).toUInt64
/-- `LVL_DEPTH` 9 for `HZ > 100` (:175). -/
def LVL_DEPTH : Nat := 9
/-- `WHEEL_TIMEOUT_CUTOFF` and `WHEEL_TIMEOUT_MAX` (:180-181). -/
def WHEEL_TIMEOUT_CUTOFF : UInt64 := LVL_START LVL_DEPTH
def WHEEL_TIMEOUT_MAX : UInt64 := WHEEL_TIMEOUT_CUTOFF - (LVL_GRAN (LVL_DEPTH - 1)).toUInt64
/-- `WHEEL_SIZE` (:188): 576 slots. -/
def WHEEL_SIZE : Nat := LVL_SIZE * LVL_DEPTH

/-- The level of a slot (`idx / LVL_SIZE`). -/
def levelOf (slot : Nat) : Nat := slot / LVL_SIZE

/-- `calc_index` (:567-582): round the expiry up to the level's granularity;
    the slot and the bucket expiry (the step at which the slot is collected). -/
def calcIndex (expires : UInt64) (lvl : Nat) : Nat × UInt64 :=
  let e := (expires >>> (LVL_SHIFT lvl).toUInt64) + 1
  (LVL_OFFS lvl + (e.toNat &&& LVL_MASK), e <<< (LVL_SHIFT lvl).toUInt64)

/-- `calc_wheel_index(expires, clk)` (:584-620): the level from
    `delta = expires - clk` by the `LVL_START` thresholds (unsigned, as the
    C's `unsigned long`), the past (`(long) delta < 0`) at the current slot,
    and the cutoff for obscene timeouts. -/
def calcWheelIndex (expires clk : UInt64) : Nat × UInt64 :=
  let delta := expires - clk
  if delta < LVL_START 1 then calcIndex expires 0
  else if delta < LVL_START 2 then calcIndex expires 1
  else if delta < LVL_START 3 then calcIndex expires 2
  else if delta < LVL_START 4 then calcIndex expires 3
  else if delta < LVL_START 5 then calcIndex expires 4
  else if delta < LVL_START 6 then calcIndex expires 5
  else if delta < LVL_START 7 then calcIndex expires 6
  else if LVL_DEPTH > 8 && delta < LVL_START 8 then calcIndex expires 7
  else if delta.toInt64 < 0 then (clk.toNat &&& LVL_MASK, clk)
  else
    let expires := if delta ≥ WHEEL_TIMEOUT_CUTOFF then clk + WHEEL_TIMEOUT_MAX else expires
    calcIndex expires (LVL_DEPTH - 1)

/-- The outcome of `__mod_timer` once the base is forwarded to `clk` and the
    new `expires` differs from the old (the same-expires return, :1085-1088,
    is the caller's): the slot is the timer's current one, so only `expires`
    changes and the list position and the stored bucket expiry are kept
    (:1123-1130); or the timer is detached if pending (:1144) and enqueued
    at the head of its new slot (:1173, :1180-1183). -/
inductive Placement where
  | kept (entry : WheelEntry)
  | enqueued (slot : Nat) (bucketExpiry : UInt64)
  deriving Repr, BEq

def place (p : Peer) (t : PeerTimer) (expires clk : UInt64) : Placement :=
  let (slot, bexp) := calcWheelIndex expires clk
  match p.wheel t with
  | some we => if we.slot == slot then .kept we else .enqueued slot bexp
  | none => .enqueued slot bexp

/-- The pass's order key (`__run_timers`, :2400-2420): ascending bucket
    expiry; at one step the highest collected level first (`while (levels--)`);
    within a slot the newest enqueue first (`hlist_add_head`, :659). -/
def runsBefore (a b : WheelEntry) : Bool :=
  timeBefore a.bucketExpiry b.bucketExpiry
  || (a.bucketExpiry == b.bucketExpiry
      && (levelOf a.slot > levelOf b.slot || (levelOf a.slot == levelOf b.slot && a.enqueued > b.enqueued)))

/-- The pending modeled timers with bucket expiry at or before `j`. -/
def due (d : Device) (j : UInt64) : List (PeerId × PeerTimer × WheelEntry) :=
  d.peerList.flatMap fun pid =>
    match d.peers.get? pid with
    | some p => PeerTimer.all.filterMap fun t =>
        (p.wheel t).bind fun we => if timeBeforeEq we.bucketExpiry j then some (pid, t, we) else none
    | none => []

/-- The next timer a pass at jiffies `j` runs: the first of `due` by
    `runsBefore`, or `none` when no modeled bucket is due. The caller detaches
    it (`expire_timers`, :1829) and runs its callback, then asks again: the
    wheel is scanned afresh after every callback (a sibling the callback
    deleted does not run; one re-armed into its own slot keeps its bucket
    expiry and runs; one moved does not). -/
def nextDue (d : Device) (j : UInt64) : Option (PeerId × PeerTimer × WheelEntry) :=
  (due d j).foldl (fun acc c => match acc with
    | none => some c
    | some a => if runsBefore c.2.2 a.2.2 then some c else some a) none

/-- Whether another pending modeled timer sits at the step `b` (a step is
    never split: the C runs a collected bucket to its end). -/
def anotherAtStep (d : Device) (b : UInt64) : Option (PeerId × PeerTimer) :=
  (due d b).find? (fun c => c.2.2.bucketExpiry == b) |>.map fun c => (c.1, c.2.1)

/-- The earliest pending modeled bucket expiry at or before `j` (the
    forward's `next_expiry` over the subset, :1008-1014). -/
def earliestDue (d : Device) (j : UInt64) : Option UInt64 :=
  (nextDue d j).map (·.2.2.bucketExpiry)

/-- The run-time invariant of a peer's timers: pending (`expires` present)
    iff slotted. `none` when it holds, else what fails. -/
def peerWheelProblem (p : Peer) : Option String :=
  PeerTimer.all.findSome? fun t =>
    if (p.timer t).isSome != (p.wheel t).isSome then
      some s!"timer {repr t}: expires {repr (p.timer t)} but wheel entry {repr (p.wheel t)}"
    else none

end Leanux.TimerWheel
