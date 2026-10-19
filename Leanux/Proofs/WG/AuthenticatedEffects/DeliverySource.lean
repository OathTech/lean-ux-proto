import Leanux.Proofs.WG.Environment.ObservationSource
import Leanux.Proofs.WG.Lifetimes.TrafficSource

/-! The five final-driver delivery sites share the original native delivery
operation. This source factor exposes its two buried callers without changing
branch order, return values, effects or stopping behavior. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Lifetimes
open Queues RxJoint.PollSource

def afterBatchWith {E : Type} (crypt send sendOne : PrefixM E Unit)
    (schedule : Option Worker → PrefixM E Unit)
    (drained : String → List Bool → PrefixM E Unit)
    (deliver : PrefixM E Unit) : PrefixM E Unit := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getAmbient).hidden.isNone then
    crypt
    send
    return
  for _ in [0:(← liftPrefix recordBudget)] do
    schedule none
    if (← liftPrefix peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then
      sendOne
    else break
  let d ← liftPrefix (liftWG getDev)
  drained "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty, d.handshakeQueueLen != 0]
  deliver

theorem afterBatch_native (crypt send sendOne : PrefixM E Unit)
    (schedule : Option Worker → PrefixM E Unit) (drained : String → List Bool → PrefixM E Unit) :
    afterBatchWith crypt send sendOne schedule drained (liftPrefix deliverSent) =
      TrafficSource.afterBatchWith crypt send sendOne schedule drained := rfl

def observeFront : Leanux.M Unit := do
  if let some d := (← getWG).dev then
    if !d.sendWorkQueue.isEmpty then unsupported "send work queued by an operation that does not wait"
  requireNoCryptWork

def observeFinish : Leanux.M (Int × Lean.Json) := do
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

theorem observe_factor : Environment.observeTail = (do observeFront; deliverSent; observeFinish) := by
  unfold Environment.observeTail observeFront
  simp only [bind_assoc]
  apply congrArg (fun f : WGWorld → Leanux.M (Int × Lean.Json) => getWG >>= f)
  funext w
  cases w.dev with
  | none => rfl
  | some d =>
    dsimp only
    by_cases pending : (!d.sendWorkQueue.isEmpty) = true
    · simp only [pending,ite_true,bind_assoc]; rfl
    · simp only [pending]; rfl

def observeWith (deliver : PrefixM E Unit) : PrefixM E (Int × Lean.Json) := do
  liftPrefix observeFront
  deliver
  liftPrefix observeFinish

private theorem lift_bind (body : Leanux.M α) (next : α → Leanux.M β) :
    (liftPrefix body >>= fun value => liftPrefix (next value) : PrefixM E β) = liftPrefix (body >>= next) := by
  funext w h
  change runPrefix (liftPrefix body >>= fun value => liftPrefix (next value)) w h =
    ((body >>= next).run w,h)
  rw [runPrefix_bind,runPrefix_lift]
  cases run : body.run w <;> simp only [StateT.run_bind,run,runPrefix_lift] <;> rfl

theorem observe_native : observeWith (liftPrefix deliverSent : PrefixM E Unit) =
    liftPrefix Environment.observeTail := by
  rw [observe_factor]
  unfold observeWith
  rw [lift_bind,lift_bind]

/-- The pre-delivery sent projection is recorded before native delivery can
Stop or clear it. The native computation is performed once, unchanged. -/
def observed (record : List SentDatagram → E) : PrefixM E Unit := do
  let w ← liftPrefix getWG
  emitPrefix (record w.sent)
  liftPrefix deliverSent

theorem observed_run (record : List SentDatagram → E) (w : World) (h : List E) :
    runPrefix (observed record) w h = (deliverSent.run w,h ++ [record w.wg.sent]) := rfl

theorem observed_appends (record : List SentDatagram → E) : Appends (observed record) :=
  fun w _ => ⟨[record w.wg.sent],rfl⟩

theorem observed_projects (ρ : E → Option F) (record : List SentDatagram → E)
    (ignored : ∀ sent, ρ (record sent) = none) :
    ProjectsPrefix ρ id (observed record) (liftPrefix deliverSent) := by
  intro w h
  rw [observed_run,runPrefix_lift]
  simp only [List.filterMap_append,List.filterMap_cons,ignored,List.filterMap_nil,List.append_nil]
  cases deliverSent.run w <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource
