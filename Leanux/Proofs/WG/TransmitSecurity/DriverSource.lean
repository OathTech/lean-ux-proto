import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceObserved
import Leanux.Proofs.WG.TransmitSecurity.NonceInitialized
import Leanux.Proofs.WG.HandshakeSecurity.ResponderStagingSource
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerSource
import Leanux.Proofs.WG.AuthenticatedEffects.CandidatePollSource
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeLifecycleSource
import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsSource
import Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffectsSource

/-! The nonce source driver parameterized at native TX boundaries. Its nonce
specialization is proved equal to the initialized observer in the companion
specialization module. Packet, ring, confirmation and encryption events share
that exact callback wiring. -/
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration Packets
open Leanux.Proofs.WG.Origins.HandshakeSources
open HandshakeSecurity.Confirmation.Poll

structure Hooks (E : Type) where
  fixtureEnter : AuthenticatedEffects.FixtureEffects.Trigger → WGPrefix E Nat := fun _ => pure 0
  fixtureLeave : Nat → WGPrefix E Unit := fun _ => pure ()
  handshake : (PeerId → WGPrefix E Bool) → (PeerId → WGPrefix E Unit) → WGPrefix E Bool :=
    AuthenticatedEffects.HandshakeWorker.source
  flushedSend : PeerId → WGPrefix E Unit := fun pid => liftWGPrefix (runFlushedSendWork pid)
  armTimer : PeerId → PeerTimer → Nat → Option UInt64 → WGPrefix E Unit :=
    fun pid timer delay caller => liftWGPrefix (WG.armTimer pid timer delay caller)
  queueSend : PeerId → WGPrefix E Unit :=
    fun pid => liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
  candidateEnter : SkbId → RxPacket → PrefixM E Nat := fun _ _ => pure 0
  candidateLeave : Nat → PrefixM E Unit := fun _ => pure ()
  stackInput : AuthenticatedEffects.GroOccurrence.Entry → PrefixM E Unit → PrefixM E Unit :=
    fun _ body => body
  prepare : PrefixM E (Option PeerId) := liftPrefix (liftWG RxWorkers.prepareSource)
  counterCheck : SkbId → RxPacket → PrefixM E Bool :=
    fun _ pkt => liftWGObserver (liftWGPrefix (counterValidate pkt.keypair pkt.nonce))
  timerSelected : Device → UInt64 → PeerId → PeerTimer → WheelEntry → PrefixM E Nat
  timerFinished : Nat → PrefixM E Unit := fun _ => pure ()
  selection : PeerId → WGPrefix E (Option (Peer × Option KeypairId))
  confirmation : PeerId → KeypairId → WGPrefix E Bool
  session : PeerId → WGPrefix E Bool
  reserve : KeypairId → WGPrefix E Nat
  allocate : List DataPacket → WGPrefix E (List SkbId)
  create : PeerId → List SkbId → WGPrefix E Unit
  front : Nat → Nat → List Packet → Nat → WGPrefix E (Except Int PeerId)
  poll : PrefixM E (Option (List SkbId))
  encrypt : Option (List SkbId) → PrefixM E Bool
  transmit : PeerId → PrefixM E Bool

/-- Scope markers for the actual guarded local-send trigger sites. -/
def fixtureOps (hooks : Hooks E) : AuthenticatedEffects.FixtureEffects.Hooks E where
  enter := hooks.fixtureEnter
  leave := hooks.fixtureLeave

/-- Only timer arms and send-work appends are callbacks; native guard steps remain fixed. -/
def effectOps (hooks : Hooks E) : AuthenticatedEffects.TimerEffects.Ops (WGPrefix E) :=
  AuthenticatedEffects.TimerEffects.observed hooks.armTimer hooks.queueSend

/-- Scheduled and directly flushed sends share the same native callback. -/
def sendWorkerObserved (hooks : Hooks E) : PrefixM E Unit :=
  HandshakeSecurity.SendExchange.oneWith liftPrefix (fun pid => liftWGObserver (hooks.flushedSend pid))

def stagingObserved (hooks : Hooks E) (pid : PeerId) : WGPrefix E Unit := do
  let some (p,keypair) ← hooks.selection pid | return
  let packets := p.staged
  let outNokey (invalid : Bool) := AuthenticatedEffects.PacketEffects.noKeyWith (effectOps hooks) pid packets keypair invalid
  if ← liftWGPrefix (branch .stagedNoKeypair keypair.isNone) then return ← outNokey false
  let some id := keypair | liftWGPrefix (invariant "unreachable")
  let k ← liftWGPrefix (getKeypair id)
  if ← liftWGPrefix (branch .stagedKeyInvalid !k.sending.isValid) then return ← outNokey false
  if ← liftWGPrefix (branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME) then
    return ← outNokey true
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← liftWGPrefix (branch .stagedNonceIterate true)
    let ds ← liftWGPrefix (ipTunnelEcnEncap pkt)
    let nonce ← hooks.reserve id
    if ← liftWGPrefix (branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then return ← outNokey true
    packetsCb := packetsCb ++ [{ peer := pid, keypair := id, nonce, plaintext := pkt, ds }]
  _ ← liftWGPrefix (branch .stagedNonceIterate false)
  liftWGPrefix (peerGet (← liftWGPrefix (IndexOwner.peerDeref (.keypair id))))
  let item ← hooks.allocate packetsCb
  hooks.create pid item

def keepaliveObserved (hooks : Hooks E) (pid : PeerId) : WGPrefix E Unit := do
  let p ← liftWGPrefix (getPeer pid)
  if ← liftWGPrefix (branch .keepaliveStagedEmpty p.staged.isEmpty) then
    if ← liftWGPrefix (branch .keepaliveNoMem !(← liftWGPrefix (hiddenAlloc .keepaliveSkb))) then return
    liftWGPrefix (setPeer pid { p with staged := p.staged ++ [{ mtu := (← liftWGPrefix getDev).mtu }] })
  (stagingObserved hooks) pid

def transmitObserved (hooks : Hooks E) (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    WGPrefix E Int := do
  match ← hooks.front family addr packets mtu with
  | .error err => pure err
  | .ok pid =>
    (stagingObserved hooks) pid
    liftWGPrefix (peerPut (some pid))
    pure 0

def expiredKeepaliveObserved (hooks : Hooks E) (pid : PeerId) : WGPrefix E Unit :=
  AuthenticatedEffects.TimerEffects.expiredKeepaliveWith (effectOps hooks) (keepaliveObserved hooks) pid

def persistentObserved (hooks : Hooks E) (pid : PeerId) : WGPrefix E Unit :=
  AuthenticatedEffects.TimerEffects.persistentWith (effectOps hooks) (keepaliveObserved hooks) pid

def timerObserved (hooks : Hooks E) (pid : PeerId) : PeerTimer → WGPrefix E Unit
  | .retransmitHandshake => AuthenticatedEffects.TimerEffects.retransmitWith (effectOps hooks) pid
  | .sendKeepalive => (expiredKeepaliveObserved hooks) pid
  | .newHandshake => AuthenticatedEffects.TimerEffects.expiredNewWith (effectOps hooks) pid
  | .zeroKeyMaterial => liftWGPrefix (expiredZeroKeyMaterial pid)
  | .persistentKeepalive => (persistentObserved hooks) pid

def handshakeOps (hooks : Hooks E) : Ops (WGPrefix E) where
  step := liftWGPrefix
  session := hooks.session
  modifyPeer := fun pid f => liftWGPrefix (do setPeer pid (f (← getPeer pid)))
  create := fun pid => liftWGPrefix (createResponse pid)
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  derived := fun pid => liftWGPrefix (timersSessionDerived pid)
  traversal := fun pid => liftWGPrefix (timersTraversal pid)
  sent := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketSent pid)
  cookie := fun msg src => liftWGPrefix (sendHandshakeCookie msg src)
  initiation := fun msg => liftWGPrefix (consumeInitiation msg)
  response := fun msg => liftWGPrefix (consumeResponse msg)
  endpoint := fun pid src => liftWGPrefix (setPeerEndpointFromSkb pid src)
  complete := fun pid => liftWGPrefix (timersHandshakeComplete pid)
  keepalive := (keepaliveObserved hooks)
  received := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketReceived pid)
  put := fun peer => liftWGPrefix (peerPut peer)
  cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)

def handshakeObserved (hooks : Hooks E) : WGPrefix E Bool :=
  hooks.handshake hooks.session (keepaliveObserved hooks)


def receiveTailObserved (hooks : Hooks E) (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    WGPrefix E (Option (List UInt8)) := do
  if ← liftWGPrefix (branch .doneReceivedNew confirmed) then
    liftWGPrefix (timersHandshakeComplete pid .walltimeLastHandshakeData)
    (stagingObserved hooks) pid
  match ← AuthenticatedEffects.PacketEffects.prepareWith (effectOps hooks) pid pkt with
  | none => pure none
  | some ready => liftWGPrefix (Packets.rxFinish pid ready)

def consumeObserved (hooks : Hooks E) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    WGPrefix E (Option (List UInt8)) := do
  liftWGPrefix (setPeerEndpoint pid ep)
  let confirmed ← hooks.confirmation pid pkt.keypair
  (receiveTailObserved hooks) pid pkt confirmed

def pollObserved (hooks : Hooks E) (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → PrefixM E Unit) : PrefixM E Nat :=
  AuthenticatedEffects.CandidatePoll.sourceWith (fun a => liftWGObserver (liftWGPrefix a))
    hooks.candidateEnter hooks.candidateLeave hooks.counterCheck
    (fun peer pkt ep => liftWGObserver ((consumeObserved hooks) peer pkt ep))
    (napiGroReceivePrefix toStack) (napiGroFlushAllPrefix toStack) pid budget

def stackObserved (hooks : Hooks E) : List UInt8 → PrefixM E Unit :=
  stackReceiveWith (receive4With (reply4With
    (fun family addr packets mtu => liftWGObserver ((transmitObserved hooks) family addr packets mtu))))

def stackFlushObserved (hooks : Hooks E) (packets : List (List UInt8)) : PrefixM E Unit :=
  packets.forM (stackObserved hooks)

def nativePollObserved (hooks : Hooks E) (pid : PeerId) (budget : Nat) : PrefixM E Nat :=
  AuthenticatedEffects.GroOccurrencePoll.observed
    (fun action => liftWGObserver (liftWGPrefix action))
    hooks.candidateEnter hooks.candidateLeave hooks.counterCheck
    (fun peer packet endpoint => liftWGObserver (consumeObserved hooks peer packet endpoint))
    hooks.stackInput (stackObserved hooks) pid budget

def softirqObserved (hooks : Hooks E) : PrefixM E Unit :=
  RxNapi.softirqWith (liftWGObserver (liftWGPrefix RxNapi.pendingSource)) (nativePollObserved hooks)

def inlinePollObserved (hooks : Hooks E) : PrefixM E Unit :=
  RxNapi.inlineWith (liftWGObserver (liftWGPrefix RxNapi.pendingSource)) (nativePollObserved hooks)

def irqExitObserved (hooks : Hooks E) : PrefixM E Unit :=
  RxNapi.irqExitWith (liftWGObserver (liftWGPrefix RxNapi.scheduledSource)) (softirqObserved hooks)

def reschedObserved {E : Type} (worker : Worker) (site : Decision) : PrefixM E Bool := do
  let yes ← liftPrefix (Env.condResched worker)
  liftPrefix (branch site yes)

def encryptTailObserved (hooks : Hooks E) (item : Option (List SkbId)) : PrefixM E IterResult :=
  workerIterPrefix .encryptWorker none (hooks.encrypt item)
    (reschedObserved .encryptWorker .encWorkerNeedResched)

def encryptIterObserved (hooks : Hooks E) : PrefixM E IterResult := do
  let item ← hooks.poll
  (softirqObserved hooks)
  (encryptTailObserved hooks) item

def txIterObserved (hooks : Hooks E) (pid : PeerId) : PrefixM E IterResult :=
  workerIterPrefix .txWorker (some pid) (hooks.transmit pid)
    (reschedObserved .txWorker .txNeedResched)

def decryptStepObserved (hooks : Hooks E) : PrefixM E Bool :=
  RxWorkers.decryptWith hooks.prepare
    (fun pid => liftPrefix (liftWG (peerPut (some pid)))) (softirqObserved hooks) (irqExitObserved hooks)

def decryptIterObserved (hooks : Hooks E) : PrefixM E IterResult :=
  workerIterPrefix .decryptWorker none (decryptStepObserved hooks)
    (reschedObserved .decryptWorker .decWorkerNeedResched)

def receiveIterObserved (hooks : Hooks E) : PrefixM E IterResult :=
  workerIterPrefix .receiveWorker none (liftWGObserver (handshakeObserved hooks))
    (liftPrefix (Env.condResched .receiveWorker))

def cryptAheadObserved (hooks : Hooks E) (pid : PeerId) : PrefixM E Unit := do
  if (← liftPrefix getAmbient).hidden.isNone then return
  let some item := (← liftPrefix (liftWG (getPeer pid))).txQueue.all.head? | return
  let some id := item.head? | liftPrefix (invariant "an empty ring item")
  if (← liftPrefix (liftWG (getTxSkb id))).state != .uncrypted then return
  let next ← liftPrefix peekHiddenSite
  unless next == some HiddenSite.modTimerArm.info.id || next == some HiddenSite.timerJiffiesTraversal.info.id do return
  let some enc := (← liftPrefix getAmbient).suspended.find? (·.worker == .encryptWorker)
    | liftPrefix (throw (.hidden "the tx worker's head is uncrypted and no encrypt activation is suspended, but the next record is the traversal timer's caller read or arm (site 426 or 100)"))
  liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}))
  let r ← (encryptIterObserved hooks)
  liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))
  match r with
  | .continued =>
    liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended.map fun x =>
      if x == enc then {x with iterations := x.iterations + 1} else x})
  | .ended => liftPrefix (throw (.hidden "the encrypt activation's queue is empty, but the next record is the traversal timer's caller read or arm (site 426 or 100)"))
  | .yielded => liftPrefix (invariant "the encrypt activation yielded on a record that is not a resched")

def iterationObserved (hooks : Hooks E) (a : Activation) : PrefixM E IterResult := do
  match a.worker with
  | .encryptWorker => (encryptIterObserved hooks)
  | .txWorker =>
    let some pid := a.pid | liftPrefix (invariant "a tx activation without its peer")
    (cryptAheadObserved hooks) pid
    (txIterObserved hooks) pid
  | .decryptWorker => (decryptIterObserved hooks)
  | .receiveWorker => (receiveIterObserved hooks)
  | w => liftPrefix (invariant s!"{w.symbol} is not a draining worker")

def scheduleObserved (hooks : Hooks E) (stack : Option Worker) : PrefixM E Unit :=
  SourceScheduler.schedule (iterationObserved hooks) (softirqObserved hooks) stack

def cryptObserved (hooks : Hooks E) : PrefixM E Unit := do
  (scheduleObserved hooks) none
  liftPrefix Env.deliverSent

def sendWorkersObserved (hooks : Hooks E) : PrefixM E Unit := do
  if (← liftPrefix getWG).dev.isNone then return
  liftPrefix Env.requireNoCryptWork
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then liftPrefix Env.deliverSent; return
    (sendWorkerObserved hooks)
    (scheduleObserved hooks) none
  liftPrefix (budgetExhausted "the send work queue")

def afterXmitObserved (hooks : Hooks E) : PrefixM E Unit := do
  let some d := (← liftPrefix getWG).dev | return
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    liftPrefix (unsupported "wg_xmit queued crypt work and a handshake (their order)")
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if crypt then
    (cryptObserved hooks)
    let d ← liftPrefix (liftWG getDev)
    liftPrefix (Env.requireDrained "wg_xmit queued" [!d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  (sendWorkersObserved hooks)

def timerSectionObserved {E : Type} (worker : Worker) (body : PrefixM E Unit) : PrefixM E Unit := do
  if worker.timer?.isNone then liftPrefix (invariant s!"{worker.symbol} is not a timer callback")
  liftPrefix (modifyAmbient fun s => {s with fired := s.fired.push worker.symbol})
  runWorkerPrefix worker body

def timersObserved (hooks : Hooks E) (jPass : UInt64) : PrefixM E Bool := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getWG).dev.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  let mut step : Option UInt64 := none
  for _ in [0:(← liftPrefix recordBudget)] do
    let some site ← liftPrefix Env.peekNextSite | break
    let d ← liftPrefix (liftWG getDev)
    if let some w := Env.timerSectionOf site then
      if w == .clearPeerWorker then
        if let some b := step then
          liftPrefix (Env.requireStepComplete b)
          step := none
        if d.clearWorkQueue.isEmpty then break
        liftPrefix Env.runOneClearWorker
      else
        let some (pid, t, we) := TimerWheel.nextDue d jPass
          | liftPrefix (throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jPass}"))
        let timerToken ← hooks.timerSelected d jPass pid t we
        let expected ← liftPrefix (Env.timerWorker t)
        if w != expected then
          liftPrefix (throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}"))
        if let some u ← liftPrefix (peekUnit w) then
          match (← liftPrefix getWG).timerUnits.find? (·.1 == u) with
          | some (_, pid', t') =>
            if pid' != pid || t' != t then
              liftPrefix (throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}"))
          | none => liftPrefix (throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})"))
        if let some b := step then
          if b != we.bucketExpiry then liftPrefix (Env.requireStepComplete b)
        liftPrefix (liftWG (delTimer pid t))
        liftPrefix (modifyWG fun s => {s with timerPassStep := some we.bucketExpiry})
        timerSectionObserved w (liftWGObserver ((timerObserved hooks) pid t))
        liftPrefix (modifyWG fun s => {s with timerPassStep := none})
        hooks.timerFinished timerToken
        step := some we.bucketExpiry
        fired := true
    else
      if let some b := step then
        liftPrefix (Env.requireStepComplete b)
        step := none
      if !fired then break
      else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then (sendWorkerObserved hooks)
      else
        (cryptObserved hooks)
        if (← liftPrefix Env.peekNextSite) == some site then break
  if let some b := step then liftPrefix (Env.requireStepComplete b)
  if fired then
    liftPrefix Env.deliverSent
    let d ← liftPrefix (liftWG getDev)
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      liftPrefix (unsupported "work a timer queued outlived the guest's wait")
  return fired

def placeholderTimersObserved (hooks : Hooks E) (jHi : UInt64) : PrefixM E Unit := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getWG).dev.isNone then return
  let pending := (← liftPrefix (liftWG getDev)).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let d ← liftPrefix (liftWG getDev)
    let some (pid, t, we) := TimerWheel.nextDue d jHi | break
    let timerToken ← hooks.timerSelected d jHi pid t we
    liftPrefix (liftWG (delTimer pid t))
    timerSectionObserved (← liftPrefix (Env.timerWorker t)) (liftWGObserver ((timerObserved hooks) pid t))
    hooks.timerFinished timerToken
  (cryptObserved hooks)
  (sendWorkersObserved hooks)
  for _ in [0:(← liftPrefix (liftWG getDev)).clearWorkQueue.length + 1] do
    if (← liftPrefix (liftWG getDev)).clearWorkQueue.isEmpty then break
    liftPrefix Env.runOneClearWorker

def idleTimersObserved (hooks : Hooks E) : PrefixM E Unit := do
  let w ← liftPrefix getWG
  let a ← liftPrefix getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.traceBound.toUInt64 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then (placeholderTimersObserved hooks) jHi else discard <| (timersObserved hooks) jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation"))
  discard <| (timersObserved hooks) jEnd
  liftPrefix (Env.requireNothingDue jEnd)
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modifyWG fun w => {w with jiffiesLast := some j})

def afterAdvanceObserved (hooks : Hooks E) : PrefixM E Unit := do
  let w ← liftPrefix getWG
  let a ← liftPrefix getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then (placeholderTimersObserved hooks) jHi else discard <| (timersObserved hooks) jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance"))
  let some (j0, j1) := (← liftPrefix getEnv).lastAdvance | liftPrefix (invariant "afterAdvance without an advance")
  let jPass := if timeAfter jEnd j1 then jEnd else j0
  discard <| (timersObserved hooks) jPass
  liftPrefix (Env.requireNothingDue jPass)
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modifyWG fun w => {w with jiffiesLast := some j})

def receiveEntryObserved {E : Type} (msg : List UInt8) (src : SkbSource) : PrefixM E Unit :=
  liftPrefix (liftWG (wgReceive msg src))

def multicastObserved {E : Type} (family addr : Nat) : PrefixM E Unit :=
  liftPrefix (Env.xmitMulticastLoop family addr)

def drainObserved {E : Type} (what : String) (flags : List Bool) : PrefixM E Unit :=
  liftPrefix (Env.requireDrained what flags)

def injectObserved (hooks : Hooks E) (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) : PrefixM E Int :=
  TrafficSource.injectWith receiveEntryObserved (cryptObserved hooks) drainObserved family port msg tos ll dest

def afterBatchObserved (hooks : Hooks E) : PrefixM E Unit :=
  TrafficSource.afterBatchWith (cryptObserved hooks) (sendWorkersObserved hooks)
    ((sendWorkerObserved hooks)) (fun stack => (scheduleObserved hooks) stack) drainObserved

def floodObserved (hooks : Hooks E) (count port family : Nat) (messages : List (List UInt8)) : PrefixM E Int :=
  TrafficSource.floodWith receiveEntryObserved (inlinePollObserved hooks) (afterBatchObserved hooks) drainObserved count port family messages

def batchItemObserved (hooks : Hooks E) (d : Device) (cqes : List Int) (item : Env.BatchItem) : PrefixM E (ForInStep (List Int)) :=
  batchItemWith receiveEntryObserved (inlinePollObserved hooks) multicastObserved
    (fun family addr packets mtu => liftWGObserver
      (AuthenticatedEffects.FixtureEffects.runWith (fixtureOps hooks) (.transmit family addr packets mtu)
        (transmitObserved hooks family addr packets mtu))) d cqes item

def batchObserved (hooks : Hooks E) (items : List Env.BatchItem) : PrefixM E Int :=
  TrafficSource.batchWith (batchItemObserved hooks) (afterBatchObserved hooks) items

def syscallXmitObserved (hooks : Hooks E) (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) : PrefixM E Int :=
  syscallXmitWith multicastObserved
    (fun family addr packets mtu => liftWGObserver
      (AuthenticatedEffects.FixtureEffects.runWith (fixtureOps hooks) (.transmit family addr packets mtu)
        (transmitObserved hooks family addr packets mtu))) family addr payload opts

def sendDrainObserved (hooks : Hooks E) (upTo : Option PeerId) : WGPrefix E Unit :=
  HandshakeSecurity.SendExchange.drainWith liftWGPrefix hooks.flushedSend
    (fun pid => liftWGPrefix (runFlushedClearWork pid)) upTo

def removeObserved (hooks : Hooks E) (peer : Option PeerId) : WGPrefix E Unit :=
  HandshakeSecurity.SendExchange.removeWith liftWGPrefix (sendDrainObserved hooks) peer

def removeAllObserved (hooks : Hooks E) : WGPrefix E Unit :=
  HandshakeSecurity.SendExchange.removeAllWith liftWGPrefix (sendDrainObserved hooks)

def configOut {E : Type} (a : PeerAttrs) (peer : Option PeerId) (ret : Int) : WGPrefix E Int := do
  liftWGPrefix (peerPut peer)
  _ ← liftWGPrefix (branch .peerZeroPsk a.presharedKey.isSome)
  pure ret

def configTailFinish (hooks : Hooks E) (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) : WGPrefix E Int :=
  AuthenticatedEffects.FixtureEffects.peerFinishObserved (fixtureOps hooks)
    (stagingObserved hooks) (keepaliveObserved hooks) configOut a peer pid ret

def configTail (hooks : Hooks E) (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) : WGPrefix E Int :=
  peerAllowedIpsWith (fun d b => liftWGPrefix (branch d b))
    (fun ip => liftWGPrefix (setAllowedip pid ip)) (configOut a peer) a ((configTailFinish hooks) a peer pid)

def configUpdate (hooks : Hooks E) (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) : WGPrefix E Int :=
  peerConfigUpdateWith (fun {_} a => liftWGPrefix a) (removeObserved hooks peer)
    (do let p ← liftWGPrefix (getPeer pid); liftWGPrefix (setPeer pid {p with presharedKey := psk.getD []}))
    (liftWGPrefix (removeByPeer pid)) (fun e => liftWGPrefix (setPeerEndpoint pid e))
    (configOut a peer) ((configTail hooks) a peer pid) a flags psk

def configPeer (hooks : Hooks E) (a : PeerAttrs) : WGPrefix E Int :=
  setPeerCmdWith (fun {_} a => liftWGPrefix a) (fun key => liftWGPrefix (pubkeyLookup key))
    (configOut a none)
    (peerCommandAcquiredWith (fun {_} a => liftWGPrefix a)
      (fun key psk => liftWGPrefix (peerCreate key psk)) (fun pid => liftWGPrefix (peerGet pid))
      (configOut a none) ((configUpdate hooks) a)) a

def configPeers (hooks : Hooks E) (a : DeviceAttrs) : WGPrefix E Int :=
  devicePeersWith (fun {_} a => liftWGPrefix a) (configPeer hooks) a

def configKey (hooks : Hooks E) (a : DeviceAttrs) : WGPrefix E Int :=
  deviceKeyWith (fun {_} a => liftWGPrefix a) (fun key => liftWGPrefix (pubkeyLookup key))
    (fun peer => liftWGPrefix (peerPut peer)) (removeObserved hooks)
    (fun pid => liftWGPrefix (precomputeStaticStatic pid)) (fun pid => liftWGPrefix (expireCurrentPeerKeypairs pid))
    (fun pid => AuthenticatedEffects.FixtureEffects.runWith (fixtureOps hooks) (.identityConfiguration a pid)
      (stagingObserved hooks pid)) ((configPeers hooks) a) a

def configDeviceUpdate (hooks : Hooks E) (a : DeviceAttrs) (flags : UInt32) : WGPrefix E Int :=
  deviceUpdateWith (fun {_} a => liftWGPrefix a) (fun pid => liftWGPrefix (clearPeerEndpointSrc pid))
    (fun port => liftWGPrefix (setPort port)) (removeAllObserved hooks) ((configKey hooks) a) a flags

def configDevice (hooks : Hooks E) (a : DeviceAttrs) : WGPrefix E Int :=
  setDeviceWith (fun {_} a => liftWGPrefix a) ((configDeviceUpdate hooks) a) a

def openObserved (hooks : Hooks E) : WGPrefix E Int :=
  AuthenticatedEffects.FixtureEffects.openObserved (fixtureOps hooks)
    (stagingObserved hooks) (keepaliveObserved hooks)

def upObserved (hooks : Hooks E) : WGPrefix E Int := do
  liftWGPrefix (modifyDev fun d => {d with running := true})
  let ret ← (openObserved hooks)
  if ret < 0 then liftWGPrefix (modifyDev fun d => {d with running := false})
  pure ret

def envUpObserved (hooks : Hooks E) : PrefixM E Int := do
  let some d := (← liftPrefix getWG).dev | return -ENODEV
  if d.running then return 0
  let ret ← liftWGObserver (upObserved hooks)
  liftPrefix (skipCut allocCuts)
  if ret == 0 then
    liftPrefix Net.Fib.rtCacheFlush
    liftPrefix (Net.Fib.netdevUp WG0_IFINDEX)
  if ret == 0 then liftPrefix (modifyEnv fun w => {w with routesPending := true})
  pure ret

def downObserved (hooks : Hooks E) : WGPrefix E Unit :=
  HandshakeSecurity.SendExchange.downWith liftWGPrefix (sendDrainObserved hooks)

def destructObserved (hooks : Hooks E) : WGPrefix E Unit :=
  HandshakeSecurity.SendExchange.destructWith liftWGPrefix (sendDrainObserved hooks)

def envDownObserved (hooks : Hooks E) : PrefixM E Int :=
  HandshakeSecurity.SendExchange.envDownWith liftPrefix (liftWGObserver (downObserved hooks))

def envDeleteObserved (hooks : Hooks E) : PrefixM E Int :=
  HandshakeSecurity.SendExchange.envDeleteWith liftPrefix
    (liftWGObserver (downObserved hooks)) (liftWGObserver (destructObserved hooks))

def retainedObserved (hooks : Hooks E) (call : Syscall) : PrefixM E Int :=
  match call with
  | .wgUp => socketCallOnWith (fun {_} a => liftPrefix a) SENDER_FD (envUpObserved hooks)
  | .wgDown => socketCallOnWith (fun {_} a => liftPrefix a) SENDER_FD (envDownObserved hooks)
  | _ => liftPrefix (Leanux.dispatch call)

def observeObserved (hooks : Hooks E) : PrefixM E (Int × Lean.Json) := do
  (idleTimersObserved hooks)
  liftPrefix Environment.observeTail

def dispatchObserveObserved (hooks : Hooks E) : PrefixM E Int := do
  let (ret, observed) ← (observeObserved hooks)
  liftPrefix (modifyAmbient fun w => {w with extraOut := ["datagrams","replies","stats"].map fun k => (k,observed.getObjValD k)})
  socketCallOnWith (fun {_} a => liftPrefix a) LISTEN4_FD (pure ret)

def dispatchSetObserved (hooks : Hooks E) (attrs : DeviceAttrs) : PrefixM E Int :=
  netlinkRequestWith (fun {_} a => liftPrefix a) (liftWGObserver ((configDevice hooks) attrs))

def dispatchCreateObserved {E : Type} : PrefixM E Int :=
  rtnetlinkRequestWith (fun {_} a => liftPrefix a) (liftPrefix (liftWG wgCreate))

def dispatchDeleteObserved (hooks : Hooks E) : PrefixM E Int :=
  rtnetlinkRequestWith (fun {_} a => liftPrefix a) (envDeleteObserved hooks)

def dispatchObserved (hooks : Hooks E) (call : Syscall) : PrefixM E Int :=
  dispatchWith (retainedObserved hooks) (dispatchSetObserved hooks) dispatchCreateObserved (dispatchDeleteObserved hooks)
    (syscallXmitObserved hooks) (fun family port message tos ll dest =>
      socketCallOnWith (fun {_} a => liftPrefix a) SENDER_FD ((injectObserved hooks) family port message tos ll dest))
    (floodObserved hooks) (batchObserved hooks) (dispatchObserveObserved hooks) call

def syscallObserved (hooks : Hooks E) (call : Syscall) : PrefixM E Int :=
  syscallWith (fun {_} a => liftPrefix a) ((dispatchObserved hooks) call)
    (sendWorkersObserved hooks) (idleTimersObserved hooks) (liftPrefix Env.routeIntoWg0)
    (afterXmitObserved hooks) (afterAdvanceObserved hooks) (liftPrefix Env.netnsCleanup) call

def executeObserved (hooks : Hooks E) (trace : Runner.Trace) (placeholders : Bool) : PrefixOuter E Lean.Json :=
  RxHistory.executeTraceWith (syscallObserved hooks) trace placeholders

def nonceHooks : Hooks Nonce.Allocation where
  timerSelected := fun _ _ _ _ _ => pure 0
  selection := fun pid => liftWGPrefix (HandshakeSecurity.Responder.selectionPrefix pid)
  confirmation := fun pid kid => liftWGPrefix (receivedWithKeypair pid kid)
  session := fun pid => liftWGPrefix (beginSession pid)
  reserve := Nonce.reserveObserved
  allocate := fun packets => liftWGPrefix (packets.mapM newTxSkb)
  create := fun pid item => liftWGPrefix (createData pid item)
  front := fun family addr packets mtu => liftWGPrefix (txFront family addr packets mtu)
  poll := liftPrefix (liftWG TxRing.pollSource)
  encrypt := fun item => liftPrefix (RxWorkers.encryptStepTailSource item)
  transmit := fun pid => liftPrefix (liftWG (txStep pid))

end Leanux.Proofs.WG.TransmitSecurity.Driver
