import Leanux.Proofs.WG.AuthenticatedEffects.SendWorkFrames
import Leanux.Proofs.WG.Lifetimes.HandshakeSend

/-! One callback-parametric native handshake-send spine. Exchange receipts and
causal scopes can observe these same cuts, including direct removal drains. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.SendExchange
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Ops (m : Type → Type) where
  step : {α : Type} → WG.M α → m α
  create : PeerId → m (Option (List UInt8))
  mac : PeerId → List UInt8 → m (List UInt8)
  traversal : PeerId → m Unit
  sent : PeerId → m Unit
  send : PeerId → List UInt8 → m Unit
  initiated : PeerId → m Unit
  put : Option PeerId → m Unit

def original : Ops WG.M where
  step := id
  create := createInitiation
  mac := addMacToPacket
  traversal := timersTraversal
  sent := timersAnyAuthenticatedPacketSent
  send := sendBufferToPeer
  initiated := timersHandshakeInitiated
  put := peerPut

def sendWith {m : Type → Type} [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  if ← o.step (branchExpired .initRateLimited (← o.step (getPeer pid)).lastSentHandshake REKEY_TIMEOUT (!·)) then return
  let now ← o.step (hiddenClock64 .initLastSent)
  o.step (setPeer pid {(← o.step (getPeer pid)) with lastSentHandshake := now})
  let created ← o.create pid
  if ← o.step (branch .initCreated created.isSome) then
    let some msg := created | o.step (invariant "unreachable")
    let msg ← o.mac pid msg
    o.traversal pid
    o.sent pid
    let now ← o.step (hiddenClock64 .initLastSentAgain)
    o.step (setPeer pid {(← o.step (getPeer pid)) with lastSentHandshake := now})
    o.send pid msg
    o.initiated pid

def workerWith {m : Type → Type} [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  sendWith o pid
  o.put (some pid)

theorem send_factor (pid : PeerId) : sendWith original pid = sendHandshakeInitiation pid := by
  rfl
theorem worker_factor (pid : PeerId) : workerWith original pid = handshakeSendWorker pid := by
  rfl

def afterTakeWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (worker : PeerId → m Unit) (pid : PeerId) : m Unit := do
  let p ← step (getPeer pid)
  if !p.handshakePending then step (invariant "queued work without a pending flag")
  let d ← step getDev
  step (setPeer pid {p with handshakePending := d.sendWorkQueue.contains pid})
  _ ← step (hidden (.sectionStart .sendWorker))
  worker pid
  _ ← step (hidden (.sectionStop .sendWorker))

def flushedWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (worker : PeerId → m Unit) (pid : PeerId) : m Unit := do
  step (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})
  afterTakeWith step worker pid

theorem afterTake_factor (pid : PeerId) :
    afterTakeWith (fun {_} a => a) handshakeSendWorker pid =
      AuthenticatedEffects.SendWorkCauses.afterTake pid := rfl
theorem flushed_factor (pid : PeerId) :
    flushedWith (fun {_} a => a) handshakeSendWorker pid = runFlushedSendWork pid := rfl

def oneWith {m : Type → Type} [Monad m]
    (step : {α : Type} → Leanux.M α → m α) (flushed : PeerId → m Unit) : m Unit := do
  let pid ← step AuthenticatedEffects.SendWorkCauses.select
  flushed pid

theorem one_factor : oneWith (fun {_} a => a) (fun pid => Leanux.liftWG (runFlushedSendWork pid)) =
    Env.runOneSendWorker := AuthenticatedEffects.SendWorkCauses.select_factor.symm

def drainWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (send clear : PeerId → m Unit) (upTo : Option PeerId) : m Unit := do
  for _ in [0:4096] do
    let d ← step getDev
    if d.sendWorkQueue.isEmpty && d.clearWorkQueue.isEmpty then return
    match ← step (peekUnit .sendWorker) with
    | some u =>
      let pid ← step (resolveUnit .sendWorker u d.sendWorkQueue)
      send pid
    | none =>
      match ← step (peekUnit .clearPeerWorker) with
      | some u =>
        let pid ← step (resolveUnit .clearPeerWorker u d.clearWorkQueue)
        clear pid
        if upTo == some pid then return
      | none =>
        if (← step getAmbient).hidden.isSome then
          step (throw (.hidden s!"a flush of handshake_send_wq must run queued work ({d.sendWorkQueue.length} send, {d.clearWorkQueue.length} clear items), but no section names it"))
        match d.sendWorkQueue.head?, d.clearWorkQueue.head? with
        | some pid, _ => send pid
        | none, some pid =>
          clear pid
          if upTo == some pid then return
        | none, none => return
  step (invariant "handshake_send_wq did not drain")

theorem drain_factor (upTo : Option PeerId) :
    drainWith (fun {_} a => a) runFlushedSendWork runFlushedClearWork upTo =
      drainHandshakeSendWq upTo := rfl

end Leanux.Proofs.WG.HandshakeSecurity.SendExchange
