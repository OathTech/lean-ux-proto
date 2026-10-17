import Leanux.Env

/-! The original observation continuation after its idle-timer call. This source
factor retains the complete JSON and consumes no tracked resident object. -/
namespace Leanux.Proofs.WG.Environment
open Leanux Leanux.WG Leanux.Env

def observeTail : Leanux.M (Int × Lean.Json) := do
  if let some d := (← getWG).dev then
    if !d.sendWorkQueue.isEmpty then unsupported "send work queued by an operation that does not wait"
  requireNoCryptWork
  deliverSent
  let w ← getEnv
  let foreignCreator := (← getRouting).foreignCreator
  let hex (bs : List UInt8) : String := String.join (bs.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])
  -- the guest reports type 0 for a datagram shorter than 4 bytes
  let type (bs : List UInt8) : Nat := if bs.length ≥ 4 then WG.u32le bs 0 else 0
  -- W8: after wg_netns_close the listeners are closed: `recvfrom(4)` is
  -- -EBADF and the datagrams are null (the guest prints null)
  let closed := foreignCreator && w.netnsCHolders.isEmpty
  let ret : Int := if closed then -EBADF else match w.listenerV4 with
    | (_, bs) :: _ => bs.length
    | [] => -EAGAIN
  -- W5: each datagram with the TOS / traffic class the listener's cmsg
  -- reports (`IP_RECVTOS`, `IPV6_RECVTCLASS`): the outer DS field wg0 sent
  -- Ordered as the harness orders Linux's (harness/linux.py attach_observed):
  -- a stable sort by peer key (the listener's family and the message's index
  -- word at byte 4), keeping arrival order within a peer's session and
  -- leaving the cross-peer interleaving free (pre-release review, finding 5)
  let indexWord (bs : List UInt8) : Nat := if bs.length ≥ 8 then WG.u32le bs 4 else 0
  let keyLt (a b : Nat × Nat × Nat) : Bool :=
    a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))
  let stableSortBy {α : Type} (key : α → Nat × Nat × Nat) (xs : List α) : List α :=
    ((((List.range xs.length).zip xs).toArray.qsort fun (i, a) (j, b) => keyLt (key a) (key b) || (key a == key b && i < j)).map (·.2)).toList
  let datagrams := stableSortBy (fun (f, _, bs) => (f, indexWord bs, 0))
    ((w.listenerV4.map fun (ds, bs) => (4, ds, bs)) ++ (w.listenerV6.map fun (ds, bs) => (6, ds, bs)))
  let entries := datagrams.map fun (f, ds, bs) =>
    Lean.toJson [Lean.toJson f, Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson ds, Lean.toJson (hex bs)]
  -- the sender's `recvmsg` source: a `sockaddr_in6` (SEND_FD is an IPv6
  -- socket), where an IPv4 source appears v4-mapped (::ffff:a.b.c.d), with
  -- its scope id (0: no kept source is link-local), then the TOS and the
  -- destination `IPV6_PKTINFO` reports (W5)
  let inbox := stableSortBy
    (fun dg => ((if dg.family == AF_INET then 0xffff00000000 + dg.addr else dg.addr), dg.port, indexWord dg.bytes))
    w.senderInbox
  let replies := inbox.map fun dg => let bs := dg.bytes
    let addr6 := if dg.family == AF_INET then 0xffff00000000 + dg.addr else dg.addr
    Lean.toJson [Lean.toJson AF_INET6, Lean.toJson (hex (beBytes addr6 16)), Lean.toJson dg.port, Lean.toJson (0 : Nat),
                 Lean.toJson dg.tos, Lean.toJson (hex (beBytes dg.dst 16)),
                 Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson (if bs.length ≥ 12 then WG.u32le bs 8 else 0),
                 Lean.toJson (hex bs)]
  modifyEnv fun w => { w with listenerV4 := [], listenerV6 := [], senderInbox := [] }
  -- L: without wg0 the guest's RTM_GETLINK fails with ENODEV: `stats` null
  let stats := match (← getWG).dev with
    | some d => Lean.Json.mkObj [("tx_errors", Lean.toJson d.txErrors), ("tx_dropped", Lean.toJson d.txDropped),
                                 ("rx_frame_errors", Lean.toJson d.rxFrameErrors),
                                 ("rx_length_errors", Lean.toJson d.rxLengthErrors),
                                 -- W5 (2.6): the device tstats; no transmit count in the driver
                                 ("rx_packets", Lean.toJson d.rxPackets), ("rx_bytes", Lean.toJson d.rxBytes),
                                 ("tx_packets", Lean.toJson d.txPackets), ("tx_bytes", Lean.toJson d.txBytes)]
    | none => Lean.Json.null
  return (ret, Lean.Json.mkObj [
    ("datagrams", if closed then Lean.Json.null else Lean.Json.arr entries.toArray),
    ("replies", Lean.Json.arr replies.toArray),
    ("stats", stats)])

theorem observe_eq : Env.observe = (do Env.idleTimers; observeTail) := rfl

end Leanux.Proofs.WG.Environment
