import Leanux.WG.Device
import Leanux.WG.Receive

/-!
# The environment model: the harness fixture and the WireGuard kworker

Not a mirror of C. This module holds what the trace's environment does, so
the mirror proper (`Leanux/WG`) contains only the C's data and control flow:
- the network fixture's listener port and the `wg_observe` operation, which
  waits, drains the fixture's listeners and reports wg0's counters;
- the fixture checks around `wg_up` (the device goes up once; its port must
  not be the fixture's);
- the contract of the handshake kworker (`wg_packet_handshake_send_worker`),
  applied when `wg_observe` has waited for it. It runs outside the trace's
  KCOV coverage and reports no decisions.
-/

namespace Leanux.Env
open Leanux Leanux.WG

/-- The fixture's UDP listeners are on 127.0.0.1 and ::1 at this port. -/
def LISTEN_PORT : Nat := 51999

/-- The fixture's sender (`wg_inject`) is bound to this port on `[::]`
    (dual-stack); `wg_observe` drains what it received. -/
def SENDER_PORT : Nat := 51998

/-- Whether an endpoint is the fixture's sender. -/
def isSender (family addr port : Nat) : Bool :=
  port == SENDER_PORT && ((family == AF_INET && addr == 0x7f000001) || (family == AF_INET6 && addr == 1))

/-- What the sender's datagrams carry in their skb: loopback source and
    destination, the sender's port, and the loopback interface (ifindex 1). -/
def senderSource (family : Nat) : M SkbSource :=
  if family == 4 then pure { family := 4, saddr := 0x7f000001, sport := SENDER_PORT, daddr := 0x7f000001, iif := 1 }
  else if family == 6 then pure { family := 6, saddr := 1, sport := SENDER_PORT, daddr := 1, iif := 1 }
  else unsupported "an injection family other than IPv4 or IPv6"

/-- The guest waits `OBSERVE_WAIT_US` (0.4 s) after every injection, and
    fails any trace that runs longer than `REKEY_BOUND_NS` (4 s) after
    `wg_up`. So two consumed initiations are at least 0.4 s apart (and the
    first comes long after boot), and only a timer of more than 4 s cannot
    expire within the trace. -/
def INJECT_GAP_NS : Nat := 400000000
def TRACE_BOUND_SECONDS : Nat := 4

def timing : Timing where
  sinceLastConsumption ns := ns ≤ INJECT_GAP_NS
  timerMayExpire s := s ≤ TRACE_BOUND_SECONDS

/-- Whether an endpoint is one of the fixture's listeners. -/
def listenerFamily (e : Endpoint) : Option Nat :=
  if e.port != LISTEN_PORT then none
  else if e.family == AF_INET && e.addr == 0x7f000001 then some 4
  else if e.family == AF_INET6 && e.addr == 1 then some 6
  else none

/-- The handshake worker's contract, for each peer whose work is queued,
    once `wg_observe` has waited for it: `last_sent_handshake` becomes
    current, and an initiation (148 bytes) is sent to the endpoint iff
    `wg_noise_handshake_create_initiation` succeeds, which is iff the device
    has an identity and the precomputed static-static is nonzero (with a
    low-order remote key the ephemeral DH is zero too). It is sent if the peer
    has an endpoint (else `wg_socket_send_skb_to_peer` fails with
    -EAFNOSUPPORT), and a sent initiation adds to `tx_bytes`. The worker drops
    the reference the queueing took. Endpoints other than loopback would route
    back into wg0 from the worker; they are outside the domain. -/
def runHandshakeWorkers : M Unit := do
  let d ← getDev
  for (pid, p) in d.peers.toList do
    if !p.handshakePending then continue
    let created := d.staticIdentity.hasIdentity && p.precomputedStaticStatic != List.replicate 32 0
    -- wg_socket_send_skb_to_peer: with no endpoint, -EAFNOSUPPORT and no bytes
    let sent := created && p.endpoint.isSome
    if let some e := p.endpoint then
      -- the initiation's sender index is random, and the sender reports it
      if created && isSender e.family e.addr e.port then unsupported "a handshake initiation to the fixture's sender"
      let loopback := (e.family == AF_INET && e.addr / 2 ^ 24 == 127) || (e.family == AF_INET6 && e.addr == 1)
      if created && !loopback then unsupported "a handshake sent to a non-loopback endpoint"
    if p.refcount < 2 then invariant "the worker's reference is missing"
    setPeer pid { p with handshakePending := false, lastSentExpired := false, refcount := p.refcount - 1,
                         indexed := p.indexed || created,
                         handshakeState := if created then 1 else p.handshakeState,   -- CREATED_INITIATION
                         txBytes := p.txBytes + (if sent then MESSAGE_HANDSHAKE_INITIATION_LEN else 0) }
    if sent then
      let some e := p.endpoint | invariant "unreachable"
      match listenerFamily e with
      | some 4 => modify fun w => { w with listenerV4 := w.listenerV4 ++ [MESSAGE_HANDSHAKE_INITIATION_LEN] }
      | some _ => modify fun w => { w with listenerV6 := w.listenerV6 ++ [MESSAGE_HANDSHAKE_INITIATION_LEN] }
      | none => pure ()

/-- `wg_up` as the fixture performs it: once, on a port that is not the
    fixture's own, then `dev_change_flags` (the mirror's `wgUp`). -/
def wgUp : M Int := do
  let d ← getDev
  if d.running then unsupported "wg0 is already up (the fixture's routes exist)"
  if d.incomingPort == LISTEN_PORT then unsupported "wg0's port is the fixture's listener port"
  if d.incomingPort == SENDER_PORT then unsupported "wg0's port is the fixture's sender port"
  WG.wgUp

/-- `wg_observe`: the fixture waited for the handshake workers; its
    `recvfrom` on the IPv4 listener returns the first datagram there. The
    observation also lists every datagram both listeners hold (drained), the
    datagrams the sender received (length, type, receiver index; drained), and
    wg0's transmit counters. Datagrams wg0 sent from the receive path
    (`World.sent`) reach the sender; any other destination is outside the
    domain. -/
def observe : M (Int × Lean.Json) := do
  runHandshakeWorkers
  let w ← get
  let mut received : List (Nat × Nat × Nat) := []
  for (family, addr, port, len, type, receiver) in w.sent do
    if !isSender family addr port then unsupported "a datagram sent to an endpoint other than the fixture's sender"
    received := received ++ [(len, type, receiver)]
  let replies := (received.toArray.qsort fun a b => [a.1, a.2.1, a.2.2] < [b.1, b.2.1, b.2.2]).toList
  modify fun w => { w with sent := [] }
  let ret : Int := match w.listenerV4 with
    | n :: _ => n
    | [] => -EAGAIN
  let datagrams := (w.listenerV4.map fun n => (4, n)) ++ (w.listenerV6.map fun n => (6, n))
  let sorted := (datagrams.toArray.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)).toList
  modify fun w => { w with listenerV4 := [], listenerV6 := [] }
  let d ← getDev
  return (ret, Lean.Json.mkObj [
    ("datagrams", Lean.toJson (sorted.map fun (f, n) => [f, n, 1])),   -- MESSAGE_HANDSHAKE_INITIATION
    ("replies", Lean.toJson (replies.map fun (n, t, r) => [n, t, r])),
    ("stats", Lean.Json.mkObj [("tx_errors", Lean.toJson d.txErrors), ("tx_dropped", Lean.toJson d.txDropped)])])

/-- `wg_inject`: the fixture's sender sends one datagram to `port` on 127.0.0.1
    or ::1. Only wg0's own socket is in the domain: wg0 up, on that port.
    Loopback delivers it in softirq inside the `sendto`, and the guest waits
    for the handshake worker. -/
def inject (family port : Nat) (msg : List UInt8) : M Int := do
  let d ← getDev
  if !d.running || port != d.incomingPort then unsupported "a datagram to a port other than wg0's"
  -- a pending send worker inserts an index entry under a random index
  for pid in d.peerList do requireNotPending pid "receiving while a handshake is queued"
  WG.wgReceive msg (← senderSource family)
  -- the queued receive work runs before the guest's wait ends
  if !(← getDev).handshakeQueue.isEmpty then WG.handshakeReceiveWorker
  return msg.length   -- udp_sendmsg returns the datagram's length

end Leanux.Env
