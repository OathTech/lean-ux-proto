import Leanux.Runner

/-!
# The fixed-width counters' wraps

Counters the C keeps in machine words wrap where an unbounded natural
would not. Until 2026-10-20 the mirror held three such words on WireGuard's
paths as naturals, a divergence the binary track's executed comparison of
the mirror with the compiled kernel found at the first of them; none is
reachable by a trace on this fixture (2^32 configuration calls, 2^64 table
mutations), so the differential check cannot show any, and this test is the
witness (docs/2026-10-20-fixed-width-audit.md). From each word's maximum,
one increment leaves 0, as the C does:

- `struct allowedips::seq`, a `u64` (allowedips.h:32), set to 1 by
  `wg_allowedips_init` (allowedips.c:255) and pre-incremented by every free
  (:262), insert (:287, :298) and remove-by-peer (:311); the device dump
  takes it at a split peer's first visit and abandons the peer's allowed-IPs
  nest on a change (netlink.c:166-168). An insert of an invalid prefix of
  each family returns `-EINVAL` (allowedips.c:186-187) after the increment;
  a free of the empty table increments too.
- `wg_device::device_update_gen`, an `unsigned int` (device.h:54), 1 at
  `wg_newlink` (device.c:323) and pre-incremented by every `wg_set_device`
  that passes its permission checks (netlink.c:523); the dump copies it into
  the callback's `unsigned int seq` and compares it with `prev_seq`
  (include/linux/netlink.h:292, include/net/netlink.h:1196-1198) to flag
  `NLM_F_DUMP_INTR`. A set with no attributes increments and returns 0.
- `net->ipv4.rt_genid`, an `atomic_t` (include/net/netns/ipv4.h:276),
  incremented by `rt_cache_flush` (route.c:406-409) and compared by the
  peers' endpoint caches (`rt_cache_valid`, route.c:1602-1607). One flush
  increments it.

Run: `lake build leanux-fixed-width-tests && .lake/build/bin/leanux-fixed-width-tests`.
-/

open Leanux Leanux.WG Leanux.Runner

def fixture : WGWorld :=
  { (initialWG true) with portBound := Env.portBound, fixtureNetDevices := Env.fixtureNetDevices }

def initialAmbient : Ambient := { env := harnessEnv, timing := Env.timing, hidden := some [] }

/-- The fixture with the allowed-IPs counter at the word's maximum. -/
def seqAtMaximum : WGWorld :=
  { fixture with dev := fixture.dev.map fun d =>
      { d with peerAllowedips := { d.peerAllowedips with seq := 0xFFFFFFFFFFFFFFFF } } }

/-- The fixture with the device generation at the word's maximum. -/
def genAtMaximum : WGWorld :=
  { fixture with dev := fixture.dev.map fun d => { d with deviceUpdateGen := 0xFFFFFFFF } }

/-- The fixture with the IPv4 route generation at the word's maximum. -/
def rtGenidAtMaximum : WGWorld :=
  { fixture with routing := { fixture.routing with fib4 := { fixture.routing.fib4 with rtGenid4 := 0xFFFFFFFF } } }

/-- A mutation's return and the counter it leaves, printed: the same text
    whichever type the mirror gives the counter. -/
def mutate (w : WGWorld) (m : WG.M Int) (counter : WGWorld → Option String) : Option (Int × String) := do
  let .ok ((ret, w'), _) := (m.run w).run initialAmbient | none
  return (ret, ← counter w')

def allowedipsSeq (w : WGWorld) : Option String := w.dev.map fun d => toString d.peerAllowedips.seq
def deviceGen (w : WGWorld) : Option String := w.dev.map fun d => toString d.deviceUpdateGen
def rtGenid (w : WGWorld) : Option String := some (toString w.routing.fib4.rtGenid4)

/-- Each case: its name, the world, the mutation, the counter read and the
    expected return. -/
def cases : List (String × WGWorld × WG.M Int × (WGWorld → Option String) × Int) :=
  [("allowedips.seq: insert v4 /33", seqAtMaximum, Leanux.WG.insert 4 0 33 1, allowedipsSeq, -EINVAL),
   ("allowedips.seq: insert v6 /129", seqAtMaximum, Leanux.WG.insert 6 0 129 1, allowedipsSeq, -EINVAL),
   ("allowedips.seq: free of the empty table", seqAtMaximum, (do Leanux.WG.free; return 0), allowedipsSeq, 0),
   ("device_update_gen: wg_set_device with no attributes", genAtMaximum, wgSetDevice {}, deviceGen, 0),
   ("rt_genid: rt_cache_flush", rtGenidAtMaximum, (do liftRouting Net.Fib.rtCacheFlush; return 0), rtGenid, 0)]

def main : IO UInt32 := do
  let mut failures := 0
  for (name, w, m, counter, ret) in cases do
    let expected := some (ret, "0")
    let got := mutate w m counter
    if got != expected then
      IO.eprintln s!"fixed-width tests: {name} from the counter's maximum gives {repr got}, expected {repr expected} (the C's word wraps to 0)"
      failures := failures + 1
  if failures > 0 then return 1
  IO.println s!"fixed-width tests: PASS ({cases.length} increments from the counters' maxima leave 0, as the C's words do)"
  return 0
