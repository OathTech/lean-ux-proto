import Leanux.Spikes.GhostScheduler

/-! Observers for every environment path that can commit receive polling. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Spikes.Ghost
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
  if (← getK).wg.isNone then return   -- L: no device, no worker
  requireNoCryptWork
  modifyWorld fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  for _ in [0:4096] do
    if (← getDev).sendWorkQueue.isEmpty then deliverSent; return
    runOneSendWorker
    scheduleLogged   -- a crypt activation the records resume after the section
  invariant "the send work queue did not drain"

theorem runSendWorkersLogged_erases  :
    Erases (runSendWorkersLogged) (Env.runSendWorkers) := by
  unfold runSendWorkersLogged Env.runSendWorkers
  repeat' first
    | ghost_env_step

def afterXmitLogged : GhostM Unit := do
  let some d := (← getK).wg | return   -- L: no device (the send failed)
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    unsupported "wg_xmit queued crypt work and a handshake (their order)"
  modifyWorld fun w => { w with queuedThisCall := [] }   -- the call returned and slept
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

def runTimersLogged (jHi : Nat) : GhostM Bool := do
  modifyWorld fun w => { w with queuedThisCall := [] }   -- the guest slept
  -- L: without wg0 (bare fixture, or after wg_delete) no WireGuard timer
  -- exists; a timer section in the records stays unconsumed and mismatches
  -- [AGENT, int-dl merge]
  if (← getK).wg.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  for _ in [0:4096] do
    let some site ← peekNextSite | break
    let d ← getDev
    if let some w := timerSectionOf site then
      if w == .clearPeerWorker then
        if d.clearWorkQueue.isEmpty then break
        runOneClearWorker
      else
        fireTimer w jHi
        fired := true
    else if !fired then break
    else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then runOneSendWorker
    else
      -- the crypt work a timer queued, as the records order it, and a crypt
      -- activation the records resume after a section (`scheduleLogged`)
      runCryptWorkersLogged
      if (← peekNextSite) == some site then break
  if fired then
    deliverSent
    let d ← getDev
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      unsupported "work a timer queued outlived the guest's wait"
  return fired

theorem runTimersLogged_erases (jHi : Nat) :
    Erases (runTimersLogged jHi) (Env.runTimers jHi) := by
  unfold runTimersLogged Env.runTimers
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | ghost_env_step

def runTimersPlaceholderLogged (jHi : Nat) : GhostM Unit := do
  modifyWorld fun w => { w with queuedThisCall := [] }
  if (← getK).wg.isNone then return   -- L: no wg0, no timers [AGENT, int-dl merge]
  for _ in [0:64] do
    let d ← getDev
    let due := d.peerList.flatMap fun pid =>
      match d.peers.get? pid with
      | some p => PeerTimer.all.filterMap fun t => (p.timer t).bind fun e => if e < jHi then some (e, pid, t) else none
      | none => []
    let first := due.foldl (fun acc c => match acc with
      | some a => if c.1 < a.1 then some c else some a
      | none => some c) none
    let some (_, pid, t) := first | break
    delTimer pid t
    runTimerSection (← timerWorker t) (WG.timerCallback pid t)
  runCryptWorkersLogged
  runSendWorkersLogged
  for _ in [0:64] do
    if (← getDev).clearWorkQueue.isEmpty then break
    runOneClearWorker

theorem runTimersPlaceholderLogged_erases (jHi : Nat) :
    Erases (runTimersPlaceholderLogged jHi) (Env.runTimersPlaceholder jHi) := by
  unfold runTimersPlaceholderLogged Env.runTimersPlaceholder
  repeat' first
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | with_reducible exact runTimersLogged_erases _
    | ghost_env_step
  all_goals grind only [erases_liftM]

def idleTimersLogged : GhostM Unit := do
  let w ← getWorld
  discard <| runTimersLogged (w.jiffiesLast.getD 0 + w.timing.traceBound + w.timing.advanceWait)

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
  let w ← getWorld
  let jHi := w.jiffiesLast.getD 0 + w.timing.advanceWait
  if w.hidden.isNone && w.hiddenPlaceholders then runTimersPlaceholderLogged jHi
  else discard <| runTimersLogged jHi

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
  if let some d := (← getK).wg then
    if !d.sendWorkQueue.isEmpty then unsupported "send work queued by an operation that does not wait"
  requireNoCryptWork
  deliverSent
  let w ← getWorld
  let hex (bs : List UInt8) : String := String.join (bs.map fun b =>
    let d := "0123456789abcdef".toList
    String.mk [d[b.toNat / 16]!, d[b.toNat % 16]!])
  -- the guest reports type 0 for a datagram shorter than 4 bytes
  let type (bs : List UInt8) : Nat := if bs.length ≥ 4 then WG.u32le bs 0 else 0
  -- W8: after wg_netns_close the listeners are closed: `recvfrom(4)` is
  -- -EBADF and the datagrams are null (the guest prints null)
  let closed := w.foreignCreator && w.netnsCHolders.isEmpty
  let ret : Int := if closed then -EBADF else match w.listenerV4 with
    | (_, bs) :: _ => bs.length
    | [] => -EAGAIN
  -- W5: each datagram with the TOS / traffic class the listener's cmsg
  -- reports (`IP_RECVTOS`, `IPV6_RECVTCLASS`): the outer DS field wg0 sent
  let datagrams := (w.listenerV4.map fun (ds, bs) => (4, ds, bs)) ++ (w.listenerV6.map fun (ds, bs) => (6, ds, bs))
  let entries := datagrams.map fun (f, ds, bs) =>
    Lean.toJson [Lean.toJson f, Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson ds, Lean.toJson (hex bs)]
  -- the sender's `recvmsg` source: a `sockaddr_in6` (SEND_FD is an IPv6
  -- socket), where an IPv4 source appears v4-mapped (::ffff:a.b.c.d), with
  -- its scope id (0: no kept source is link-local), then the TOS and the
  -- destination `IPV6_PKTINFO` reports (W5)
  let replies := w.senderInbox.map fun dg => let bs := dg.bytes
    let addr6 := if dg.family == AF_INET then 0xffff00000000 + dg.addr else dg.addr
    Lean.toJson [Lean.toJson AF_INET6, Lean.toJson (hex (beBytes addr6 16)), Lean.toJson dg.port, Lean.toJson (0 : Nat),
                 Lean.toJson dg.tos, Lean.toJson (hex (beBytes dg.dst 16)),
                 Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson (if bs.length ≥ 12 then WG.u32le bs 8 else 0),
                 Lean.toJson (hex bs)]
  let sortJson (xs : List Lean.Json) := (xs.toArray.qsort fun a b => a.compress < b.compress).toList
  modifyWorld fun w => { w with listenerV4 := [], listenerV6 := [], senderInbox := [] }
  -- L: without wg0 the guest's RTM_GETLINK fails with ENODEV: `stats` null
  let stats := match (← getK).wg with
    | some d => Lean.Json.mkObj [("tx_errors", Lean.toJson d.txErrors), ("tx_dropped", Lean.toJson d.txDropped),
                                 ("rx_frame_errors", Lean.toJson d.rxFrameErrors),
                                 ("rx_length_errors", Lean.toJson d.rxLengthErrors),
                                 -- W5 (2.6): the device tstats; no transmit count in the driver
                                 ("rx_packets", Lean.toJson d.rxPackets), ("rx_bytes", Lean.toJson d.rxBytes),
                                 ("tx_packets", Lean.toJson d.txPackets), ("tx_bytes", Lean.toJson d.txBytes)]
    | none => Lean.Json.null
  return (ret, Lean.Json.mkObj [
    ("datagrams", if closed then Lean.Json.null else Lean.Json.arr (sortJson entries).toArray),
    ("replies", Lean.Json.arr (sortJson replies).toArray),
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

def injectLogged (family port : Nat) (msg : List UInt8) (tos : Nat := 0) (ll : Bool := false) (dest : Nat := 0) : GhostM Int := do
  -- W8 (design 3.1, 3.4): in the foreign-creator fixture the injector lives
  -- in the creating namespace: gone after wg_netns_close, and wg0's own
  -- address (in the device namespace) is unroutable from it
  if (← getWorld).foreignCreator then
    if (← getWorld).netnsCHolders.isEmpty then unsupported "wg_inject after wg_netns_close (no socket in the creating namespace)"
    if dest == 1 then unsupported "wg_inject to wg0's address from the creating namespace (unroutable)"
  let some d := (← getK).wg | unsupported "a datagram to a port other than wg0's (no wg0)"
  if !d.running || port != d.incomingPort then unsupported "a datagram to a port other than wg0's"
  -- a pending send worker inserts an index entry under a random index
  for pid in d.peerList do requireNotPending pid "receiving while a handshake is queued"
  fixtureSend
  let src ← senderSource family dest tos ll
  runWorkerLogged .netRx (WG.wgReceive msg src)
  -- the queued work runs before the guest's wait ends: the receive worker,
  -- the decrypt worker with the NAPI poll its packet schedules, and the
  -- crypt work they queue (a session's keepalive, staged packets on key
  -- confirmation), as the records order them
  runCryptWorkersLogged
  let d ← getDev
  requireDrained "the datagram queued"
    [!d.handshakeQueue.isEmpty, !d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty]
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

def floodLogged (count port : Nat) (messages : List (List UInt8)) : GhostM Int := do
  let some d := (← getK).wg | unsupported "a flood to a port other than wg0's (no wg0)"
  if !d.running || port != d.incomingPort then unsupported "a flood to a port other than wg0's"
  -- without records (the domain filter runs before Linux), accept the floodLogged: it
  -- is a natural harness input, inside the domain; the decay then reads the
  -- placeholder clock (a prediction only)
  if (← getWorld).hidden.isNone then
    modifyWorld fun w => { w with lastUnderLoad := some 0 }
    return 0
  let startW := (HiddenSite.sectionStart .receiveWorker).info.id
  let stopW := (HiddenSite.sectionStop .receiveWorker).info.id
  let startRx := (HiddenSite.sectionStart .netRx).info.id
  let stopRx := (HiddenSite.sectionStop .netRx).info.id
  let cuts := [startRx, stopRx, (HiddenSite.ipIdentKey).info.id, (HiddenSite.ipIdentReserve).info.id,
               (HiddenSite.flowHashSecret).info.id, (HiddenSite.udpPortDraw).info.id,
               -- the first floodLogged packet's `queue_work_on` of the receive work
               -- (dispatch order): its record sits in that packet's `net_rx`
               -- section; the mirror fills `handshakeQueue` below instead
               (HiddenSite.queued .receiveWorker).info.id]
  -- before the receive worker runs: the fixture's io_uring sends' producer
  -- `net_rx` sections and IP-layer cut draws
  let _ ← discardFloodRecords startW cuts
  -- the receive-worker section: the batchLogged is queued (the ring with the
  -- leading valids, the counter at the batchLogged's size); the leading valids go
  -- through the real worker (each packet's records, the `cond_resched`
  -- between packets), which decrements the counter per packet
  _ ← hidden (.sectionStart .receiveWorker)
  let src ← senderSource 4 0
  -- the batchLogged's producer side (wg_packet_receive per datagram, receive.c:567-568):
  -- the ring and the counter, and `wg_cpumask_next_online(&last_cpu)` per
  -- packet, which on this one-CPU kernel leaves `last_cpu` at 0
  modifyDev fun d => { d with handshakeQueue := messages.map (fun m => (m, src)),
                              handshakeQueueLen := d.handshakeQueueLen + messages.length + count,
                              handshakeLastCpu := 0 }
  handshakeReceiveWorkerLogged (nestedReschedLogged .receiveWorker)
  -- the invalid tail: its clock records fold into `last_under_load`; the
  -- counter drains to 0 (every tail packet is dequeued and dropped)
  let (last, crossed) ← floodTailEffect stopW cuts (← getWorld).lastUnderLoad
  modifyWorld fun w => { w with lastUnderLoad := last }
  modifyDev fun d => { d with handshakeQueueLen := 0 }
  _ ← hidden (.sectionStop .receiveWorker)
  if messages.isEmpty && !crossed then
    throw (.hidden "the flood did not cross the under_load threshold (no under_load record)")
  deliverSent
  return 0

theorem floodLogged_erases (count port : Nat) (messages : List (List UInt8)) :
    Erases (floodLogged count port messages) (Env.flood count port messages) := by
  unfold floodLogged Env.flood
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

def pollScheduledInlineLogged : GhostM Unit := do
  let d ← getDev
  let pending := d.peers.toList.filterMap fun (pid, p) => if p.napiScheduled then some pid else none
  if pending.length > 1 then unsupported "NAPI polls of several peers in one softirq"
  for pid in pending do
    discard <| rxPollLogged pid WG.NAPI_POLL_WEIGHT fun pkts => liftM (pkts.forM Env.deliverInner)

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
    | with_reducible exact floodLogged_erases _ _ _
    | ghost_env_step

def afterBatchLogged : GhostM Unit := do
  modifyWorld fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  if (← getWorld).hidden.isNone then
    runCryptWorkersLogged
    runSendWorkersLogged
    return
  for _ in [0:4096] do
    scheduleLogged
    if (← peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← getDev).sendWorkQueue.isEmpty then
      runOneSendWorker
    else break
  let d ← getDev
  requireDrained "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty]
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
    | with_reducible exact floodLogged_erases _ _ _
    | with_reducible exact pollScheduledInlineLogged_erases
    | ghost_env_step

def batchLogged (items : List BatchItem) : GhostM Int := do
  let some d := (← getK).wg | unsupported "a batch without wg0"
  if !d.running then unsupported "a batch with wg0 down"
  for pid in d.peerList do requireNotPending pid "a batch while a handshake is queued"
  let mut cqes : List Int := []
  for item in items do
    match item with
    | .inject family port msg =>
      if port != d.incomingPort then unsupported "a batch datagram to a port other than wg0's"
      fixtureSend
      let src ← senderSource family 0
      runWorkerLogged .netRx do
        WG.wgReceive msg src
        pollScheduledInlineLogged
      cqes := cqes ++ [(msg.length : Int)]
    | .xmit family addr payload opts =>
      -- W9: the sender's `sendto` routes on the fixture's tables; a local
      -- destination never reaches wg0
      match ← routeLookup family 0 addr with
      | .error err => cqes := cqes ++ [err]
      | .ok r =>
        if r.dev != WG0_IFINDEX then unsupported "a batch transmit to a local address (not into wg0)"
        if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
          unsupported "a transmit after an MTU change took the family's routes into wg0 down"
        fixtureSend
        match ← xmitPackets family addr payload opts with
        | .error e => cqes := cqes ++ [e]
        | .ok (pkts, mtu) =>
          xmitMulticastLoop family addr
          let ret ← WG.wgXmit family addr pkts mtu
          cqes := cqes ++ [if ret == 0 then (payload.length : Int) else ret]
  modifyWorld fun w => { w with extraOut := [("cqes", Lean.toJson cqes)] }
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
    | with_reducible exact floodLogged_erases _ _ _
    | with_reducible exact pollScheduledInlineLogged_erases
    | with_reducible exact afterBatchLogged_erases
    | ghost_env_step

end Leanux.Spikes.Ghost
