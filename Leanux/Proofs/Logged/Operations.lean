import Leanux.Proofs.Logged.Scheduler

/-! Observers for every environment path that can commit receive polling. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.Logged
open Leanux Leanux.WG Leanux.Env

macro "ghost_env_step" : tactic => `(tactic|
  first
    | with_reducible apply runWorkerLogged_erases
    | with_reducible apply handshakeReceiveWorkerLogged_erases
    | with_reducible exact nestedReschedLogged_erases _
    | with_reducible exact scheduleLogged_erases _
    | with_reducible exact runCryptWorkersLogged_erases
    | with_reducible apply rxPollLogged_erases
    | with_reducible exact napiSoftirqLogged_erases
    | ghost_step)

def runSendWorkersLogged : GhostM Unit := do
  if (← getWG).dev.isNone then return   -- L: no device, no worker
  requireNoCryptWork
  modifyWG fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  -- record-driven (review item 7): every turn runs a worker whose section
  -- consumes records; the queue may grow meanwhile (a response's initiation)
  for _ in [0:(← recordBudget)] do
    if (← getDev).sendWorkQueue.isEmpty then deliverSent; return
    runOneSendWorker
    scheduleLogged   -- a crypt activation the records resume after the section
  budgetExhausted "the send work queue"

theorem runSendWorkersLogged_erases  :
    Erases (runSendWorkersLogged) (Env.runSendWorkers) := by
  unfold runSendWorkersLogged Env.runSendWorkers
  repeat' first
    | ghost_env_step

def afterXmitLogged : GhostM Unit := do
  let some d := (← getWG).dev | return   -- L: no device (the send failed)
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    unsupported "wg_xmit queued crypt work and a handshake (their order)"
  modifyWG fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  if crypt then
    runCryptWorkersLogged
    let d ← getDev
    requireDrained "wg_xmit queued" [!d.encryptQueue.empty, !d.txWorkQueue.isEmpty]
  runSendWorkersLogged

theorem afterXmitLogged_erases  :
    Erases (afterXmitLogged) (Env.afterXmit) := by
  unfold afterXmitLogged Env.afterXmit
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | ghost_env_step

def runTimersLogged (jPass : UInt64) : GhostM Bool := do
  modifyWG fun w => { w with queuedThisCall := [] }   -- the guest slept
  -- L: without wg0 (bare fixture, or after wg_delete) no WireGuard timer
  -- exists; a timer section in the records stays unconsumed and mismatches
  -- [AGENT, int-dl merge]
  if (← getWG).dev.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  let mut step : Option UInt64 := none
  -- record-driven (review item 7): every turn consumes a section or breaks
  for _ in [0:(← recordBudget)] do
    let some site ← peekNextSite | break
    let d ← getDev
    if let some w := timerSectionOf site then
      if w == .clearPeerWorker then
        if let some b := step then
          requireStepComplete b
          step := none
        if d.clearWorkQueue.isEmpty then break
        runOneClearWorker
      else
        let some (pid, t, we) := TimerWheel.nextDue d jPass
          | throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jPass}")
        let expected ← timerWorker t
        if w != expected then
          throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}")
        -- dispatch order (docs/2026-10-11-dispatch-order.md): the timer the
        -- section names, by the address its arm record carried
        if let some u ← peekUnit w then
          match (← getWG).timerUnits.find? (·.1 == u) with
          | some (_, pid', t') =>
            if pid' != pid || t' != t then
              throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}")
          | none => throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})")
        if let some b := step then
          if b != we.bucketExpiry then requireStepComplete b
        delTimer pid t
        modifyWG fun s => { s with timerPassStep := some we.bucketExpiry }
        runTimerSection w (WG.timerCallback pid t)
        modifyWG fun s => { s with timerPassStep := none }
        step := some we.bucketExpiry
        fired := true
    else
      if let some b := step then
        requireStepComplete b
        step := none
      if !fired then break
      else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then runOneSendWorker
      else
        -- the crypt work a timer queued, as the records order it, and a crypt
        -- activation the records resume after a section (`scheduleLogged`)
        runCryptWorkersLogged
        if (← peekNextSite) == some site then break
  if let some b := step then requireStepComplete b
  if fired then
    deliverSent
    let d ← getDev
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      unsupported "work a timer queued outlived the guest's wait"
  return fired

theorem runTimersLogged_erases (jHi : UInt64) :
    Erases (runTimersLogged jHi) (Env.runTimers jHi) := by
  unfold runTimersLogged Env.runTimers
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | ghost_env_step

def runTimersPlaceholderLogged (jHi : UInt64) : GhostM Unit := do
  modifyWG fun w => { w with queuedThisCall := [] }
  if (← getWG).dev.isNone then return   -- L: no wg0, no timers [AGENT, int-dl merge]
  -- the filter's own loop (review item 7): one turn per pending timer at most
  let pending := (← getDev).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let some (pid, t, _) := TimerWheel.nextDue (← getDev) jHi | break
    delTimer pid t
    runTimerSection (← timerWorker t) (WG.timerCallback pid t)
  runCryptWorkersLogged
  runSendWorkersLogged
  for _ in [0:(← getDev).clearWorkQueue.length + 1] do
    if (← getDev).clearWorkQueue.isEmpty then break
    runOneClearWorker

theorem runTimersPlaceholderLogged_erases (jHi : UInt64) :
    Erases (runTimersPlaceholderLogged jHi) (Env.runTimersPlaceholder jHi) := by
  unfold runTimersPlaceholderLogged Env.runTimersPlaceholder
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | with_reducible exact runTimersLogged_erases _
    | ghost_env_step
  all_goals grind only [erases_liftM]

def idleTimersLogged : GhostM Unit := do
  let w ← getWG
  let a ← getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.traceBound.toUInt64 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then runTimersPlaceholderLogged jHi else discard <| runTimersLogged jHi
    return
  let some jEnd ← peekSiteU64 .jiffiesEnd
    | throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation")
  discard <| runTimersLogged jEnd
  requireNothingDue jEnd
  let j ← hiddenJiffies .jiffiesEnd
  if j != jEnd then invariant "the end-of-wait jiffies record changed between the peek and the read"
  modifyWG fun w => { w with jiffiesLast := some j }

theorem idleTimersLogged_erases  :
    Erases (idleTimersLogged) (Env.idleTimers) := by
  unfold idleTimersLogged Env.idleTimers
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | with_reducible exact runTimersLogged_erases _
    | with_reducible exact runTimersPlaceholderLogged_erases _
    | ghost_env_step

def afterAdvanceLogged : GhostM Unit := do
  let w ← getWG
  let a ← getAmbient
  if a.hidden.isNone then
    -- the domain filter's prediction (no records): the fixture's wait
    let jHi := w.jiffiesLast.getD 0 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then runTimersPlaceholderLogged jHi else discard <| runTimersLogged jHi
    return
  -- review item 7: the window ends at the recorded end of the advance's wait
  let some jEnd ← peekSiteU64 .jiffiesEnd
    | throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance")
  let some (j0, j1) := (← getEnv).lastAdvance | invariant "afterAdvance without an advance"
  let jPass := if timeAfter jEnd j1 then jEnd else j0
  discard <| runTimersLogged jPass
  requireNothingDue jPass
  let j ← hiddenJiffies .jiffiesEnd
  if j != jEnd then invariant "the end-of-wait jiffies record changed between the peek and the read"
  modifyWG fun w => { w with jiffiesLast := some j }

theorem afterAdvanceLogged_erases  :
    Erases (afterAdvanceLogged) (Env.afterAdvance) := by
  unfold afterAdvanceLogged Env.afterAdvance
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | with_reducible exact runTimersLogged_erases _
    | with_reducible exact runTimersPlaceholderLogged_erases _
    | with_reducible exact idleTimersLogged_erases
    | ghost_env_step

def observeLogged : GhostM (Int × Lean.Json) := do
  idleTimersLogged   -- the guest's wait before this operation
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

theorem observeLogged_erases  :
    Erases (observeLogged) (Env.observe) := by
  unfold observeLogged Env.observe
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | with_reducible exact runTimersLogged_erases _
    | with_reducible exact runTimersPlaceholderLogged_erases _
    | with_reducible exact idleTimersLogged_erases
    | with_reducible exact afterAdvanceLogged_erases
    | ghost_env_step
  all_goals exact erases_pure _

def injectLogged (family port : Nat) (msg : List UInt8) (tos : Nat := 0) (ll : Bool := false) (dest : Nat := 0) : GhostM Int := do
  -- W8 (design 3.1, 3.4): in the foreign-creator fixture the injector lives
  -- in the creating namespace: gone after wg_netns_close, and wg0's own
  -- address (in the device namespace) is unroutable from it
  if (← getRouting).foreignCreator then
    if (← getEnv).netnsCHolders.isEmpty then unsupported "wg_inject after wg_netns_close (no socket in the creating namespace)"
    if dest == 1 then unsupported "wg_inject to wg0's address from the creating namespace (unroutable)"
  let some d := (← getWG).dev | unsupported "a datagram to a port other than wg0's (no wg0)"
  if !d.running || port != d.incomingPort then unsupported "a datagram to a port other than wg0's"
  -- a pending send worker inserts an index entry under a random index
  for pid in d.peerList do requireNotPending pid "receiving while a handshake is queued"
  fixtureSend
  let src ← senderSource family dest tos ll
  -- lane C: the injector's `udp_sendmsg` routes the datagram in its own
  -- namespace (`ip_route_output_flow`, a wildcard source): a local route
  -- whose source is the one `senderSource` states; the loopback output
  -- creates lo's one neighbour
  if family == 4 then
    match ← Net.Fib.inSocketNs (Net.routeOutput4 0 src.daddr) with
    | .error _ => invariant "wg_inject: the injector's datagram has no route"
    | .ok r =>
      if r.dev != LO_IFINDEX || r.src != src.saddr then invariant "wg_inject: the route disagrees with the sender source"
      Net.Fib.inSocketNs (Net.neighbourClassify LO_IFINDEX)
  runWorkerLogged .netRx (WG.wgReceive msg src)
  -- the queued work runs before the guest's wait ends: the receive worker,
  -- the decrypt worker with the NAPI poll its packet schedules, and the
  -- crypt work they queue (a session's keepalive, staged packets on key
  -- confirmation), as the records order them
  runCryptWorkersLogged
  let d ← getDev
  requireDrained "the datagram queued"
    [!d.handshakeQueue.empty, !d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty]
  return msg.length   -- udp_sendmsg returns the datagram's length

theorem injectLogged_erases (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Erases (injectLogged family port msg tos ll dest) (Env.inject family port msg tos ll dest) := by
  unfold injectLogged Env.inject
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | with_reducible exact runTimersLogged_erases _
    | with_reducible exact runTimersPlaceholderLogged_erases _
    | with_reducible exact idleTimersLogged_erases
    | with_reducible exact afterAdvanceLogged_erases
    | with_reducible exact observeLogged_erases
    | ghost_env_step

def pollScheduledInlineLogged : GhostM Unit := do
  let d ← getDev
  let pending := d.peers.toList.filterMap fun (pid, p) => if p.napiScheduled then some pid else none
  if pending.length > 1 then unsupported "NAPI polls of several peers in one softirq"
  for pid in pending do
    discard <| rxPollLogged pid WG.NAPI_POLL_WEIGHT fun pkts => liftM (pkts.forM deliverInner)

theorem pollScheduledInlineLogged_erases  :
    Erases (pollScheduledInlineLogged) (Env.pollScheduledInline) := by
  unfold pollScheduledInlineLogged Env.pollScheduledInline
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | with_reducible exact runTimersLogged_erases _
    | with_reducible exact runTimersPlaceholderLogged_erases _
    | with_reducible exact idleTimersLogged_erases
    | with_reducible exact afterAdvanceLogged_erases
    | with_reducible exact observeLogged_erases
    | with_reducible exact injectLogged_erases _ _ _ _ _ _
    | ghost_env_step

def afterBatchLogged : GhostM Unit := do
  modifyWG fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  if (← getAmbient).hidden.isNone then
    runCryptWorkersLogged
    runSendWorkersLogged
    return
  -- record-driven (review item 7): every turn runs a unit whose section consumes records
  for _ in [0:(← recordBudget)] do
    scheduleLogged
    if (← peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← getDev).sendWorkQueue.isEmpty then
      runOneSendWorker
    else break
  let d ← getDev
  -- the completion guard: every queue a dispatched unit drains, as the
  -- injection path's (`injectLogged`). The handshake receive queue and its counter
  -- were omitted until 2026-10-15 (campaign 2's request 1: a constructed
  -- stream that queues the receive worker and never dispatches it was
  -- accepted). The pending-worker identity (`World.pendingWork`) is not
  -- checked here: it is the environment's dispatch bookkeeping, set only at
  -- a produce, so a pending receive worker always has a non-empty queue in
  -- the mirror's own transitions; the queue and the counter are the C's
  -- data, and a pending bit with an empty queue would be an invariant
  -- violation, not a completion fact.
  requireDrained "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty, d.handshakeQueueLen != 0]
  deliverSent

theorem afterBatchLogged_erases  :
    Erases (afterBatchLogged) (Env.afterBatch) := by
  unfold afterBatchLogged Env.afterBatch
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | with_reducible exact runTimersLogged_erases _
    | with_reducible exact runTimersPlaceholderLogged_erases _
    | with_reducible exact idleTimersLogged_erases
    | with_reducible exact afterAdvanceLogged_erases
    | with_reducible exact observeLogged_erases
    | with_reducible exact injectLogged_erases _ _ _ _ _ _
    | with_reducible exact pollScheduledInlineLogged_erases
    | ghost_env_step

def floodLogged (count port family : Nat) (messages : List (List UInt8)) : GhostM Int := do
  let some d := (← getWG).dev | unsupported "a flood to a port other than wg0's (no wg0)"
  if !d.running || port != d.incomingPort then unsupported "a flood to a port other than wg0's"
  for pid in d.peerList do requireNotPending pid "a flood while a handshake is queued"
  -- the guest's invalid template (harness/guest.c flood_prep)
  let invalid : List UInt8 := [1] ++ List.replicate 115 0 ++ List.replicate 16 0xff ++ List.replicate 16 0
  -- the floodLogged's family: the fixture sender's v4-mapped destination (wg0 sees
  -- IPv4 from 127.0.0.1) or ::1 (IPv6, the ratelimiter's /64 table)
  let src ← senderSource family 0
  for msg in messages ++ List.replicate count invalid do
    -- lane C: each send's `udp_sendmsg` routes the datagram to loopback
    -- (the batchLogged's injectLogged arm likewise) and lo's one neighbour serves it
    if family == 4 then
      match ← Net.routeOutput4 0 src.daddr with
      | .error _ => invariant "wg_flood: the datagram to wg0's port has no route"
      | .ok r =>
        if r.dev != LO_IFINDEX || r.src != src.saddr then invariant "wg_flood: the route disagrees with the sender source"
        Net.neighbourClassify LO_IFINDEX
    fixtureSend
    runWorkerLogged .netRx do
      WG.wgReceive msg src
      pollScheduledInlineLogged
  afterBatchLogged
  -- Confirm the flood's handshake queue and counter after the batch guard,
  -- which also checks them along with the other worker queues.
  let d ← getDev
  requireDrained "the flood queued" [!d.handshakeQueue.empty, d.handshakeQueueLen != 0]
  return 0

theorem floodLogged_erases (count port family : Nat) (messages : List (List UInt8)) :
    Erases (floodLogged count port family messages) (Env.flood count port family messages) := by
  unfold floodLogged Env.flood
  repeat' first
    | with_reducible exact afterBatchLogged_erases
    | with_reducible exact pollScheduledInlineLogged_erases
    | ghost_env_step

def batchLogged (items : List BatchItem) : GhostM Int := do
  let some d := (← getWG).dev | unsupported "a batch without wg0"
  if !d.running then unsupported "a batch with wg0 down"
  for pid in d.peerList do requireNotPending pid "a batch while a handshake is queued"
  let mut cqes : List Int := []
  for item in items do
    match item with
    | .inject family port msg =>
      if port != d.incomingPort then unsupported "a batch datagram to a port other than wg0's"
      fixtureSend
      let src ← senderSource family 0
      -- lane C: the sender's route to loopback and lo's one neighbour
      if family == 4 then
        match ← Net.routeOutput4 0 src.daddr with
        | .error _ => invariant "wg_batch: the datagram to wg0's port has no route"
        | .ok r =>
          if r.dev != LO_IFINDEX || r.src != src.saddr then invariant "wg_batch: the route disagrees with the sender source"
          Net.neighbourClassify LO_IFINDEX
      runWorkerLogged .netRx do
        WG.wgReceive msg src
        pollScheduledInlineLogged
      cqes := cqes ++ [(msg.length : Int)]
    | .xmit family addr payload opts =>
      -- W9: the sender's `sendto` routes on the fixture's tables; a local
      -- destination never reaches wg0
      match ← Net.routeLookup family 0 addr with
      | .error err => cqes := cqes ++ [err]
      | .ok r =>
        if r.dev != WG0_IFINDEX then unsupported "a batch transmit to a local address (not into wg0)"
        if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
          unsupported "a transmit after an MTU change took the family's routes into wg0 down"
        fixtureSend
        -- lane C: `dst_mtu` is the route's metric when it carries one
        let opts := { opts with routeMtu := opts.routeMtu <|> (if r.mtu != 0 then some r.mtu else none) }
        match ← xmitPackets family addr payload opts with
        | .error e => cqes := cqes ++ [e]
        | .ok (pkts, mtu) =>
          xmitMulticastLoop family addr
          -- lane C: `ip_finish_output2` on wg0: the device's one neighbour
          if family == 4 then Net.neighbourClassify WG0_IFINDEX
          let ret ← WG.wgXmit family addr pkts mtu
          cqes := cqes ++ [if ret == 0 then (payload.length : Int) else ret]
  modifyAmbient fun w => { w with extraOut := [("cqes", Lean.toJson cqes)] }
  afterBatchLogged
  return items.length

theorem batchLogged_erases (items : List BatchItem) :
    Erases (batchLogged items) (Env.batch items) := by
  unfold batchLogged Env.batch
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | with_reducible exact runTimersLogged_erases _
    | with_reducible exact runTimersPlaceholderLogged_erases _
    | with_reducible exact idleTimersLogged_erases
    | with_reducible exact afterAdvanceLogged_erases
    | with_reducible exact observeLogged_erases
    | with_reducible exact injectLogged_erases _ _ _ _ _ _
    | with_reducible exact pollScheduledInlineLogged_erases
    | with_reducible exact afterBatchLogged_erases
    | ghost_env_step

end Leanux.Proofs.Logged
