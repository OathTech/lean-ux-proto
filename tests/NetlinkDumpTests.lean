import Leanux.Runner

/-!
# The netlink dump's tailroom accounting (campaign 2's request 3)

`wg_get_device_dump` on the fixture's empty `wg0` (netlink.c:254-268): the
peers nest is started and cancelled, and the C's `nla_nest_cancel` trims the
chunk back to the tail saved before the nest header was put
(include/net/netlink.h:1925-1934, :1975-1978), so the chunk keeps only the
generic-netlink header, the three scalar attributes and the name: 52 bytes
of `NLMSG_GOODSIZE`, leaving 3724. Until 2026-10-19 the mirror's cancel arm
restored a snapshot taken after the header's reservation and kept a
four-byte debit (3720). The accounting is internal to the chunk: nothing is
put into the chunk after the cancel (netlink.c:264-268, `out`), so no
observation on this fixture shows it, and this test is the witness.
Run: `lake build leanux-netlink-dump-tests && .lake/build/bin/leanux-netlink-dump-tests`.
-/

open Leanux Leanux.WG Leanux.Runner

def initialWireGuard : WGWorld :=
  { (initialWG true) with portBound := Env.portBound, fixtureNetDevices := Env.fixtureNetDevices }

def initialAmbient : Ambient := { env := harnessEnv, timing := Env.timing, hidden := some [] }

/-- The dump callback's result on the empty device: its return, the chunk's
    room, whether the cursor is clear, and the messages it holds. -/
def callbackResult : Option (Int × Nat × Bool × Nat) := do
  let .ok ((out, _), _) := ((wgGetDeviceDump { hasWg := true } 0 {}).run initialWireGuard).run initialAmbient | none
  return (out.ret, out.skb.room, out.ctx.nextPeer.isNone, out.skb.messages.length)

/-- The room the C leaves: the header and the four retained attributes. -/
def cancelledNestRoom : Nat :=
  NLMSG_GOODSIZE - (nlmsgTotal 4 + nlaTotal 2 + nlaTotal 4 + nlaTotal 4 + nlaTotal 4)

def main : IO UInt32 := do
  let expected := some (0, cancelledNestRoom, true, 1)
  if cancelledNestRoom != 3724 then
    IO.eprintln s!"netlink dump tests: the C's room arithmetic is {cancelledNestRoom}, not 3724"
    return 1
  if callbackResult != expected then
    IO.eprintln s!"netlink dump tests: the cancelled peers nest leaves {repr callbackResult}, expected {repr expected} (the four-byte header debit, request 3)"
    return 1
  IO.println s!"netlink dump tests: PASS (the cancelled peers nest leaves {cancelledNestRoom} bytes, as the C does)"
  return 0
