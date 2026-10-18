import Leanux.Proofs.WG.Queues.HandshakeLoans
import Leanux.Proofs.Logged.NativeCapture

/-! Native initiation source with one callback at the timestamp branch. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

def writeTimestamp (pid : PeerId) (t : List UInt8) : WG.M Unit := do
  setPeer pid { (← getPeer pid) with latestTimestamp := t }

def timestampStep (pid : PeerId) (old t : List UInt8) : WG.M Unit := do
  if ← branch .consumeNewerTimestamp (memcmp t old == .gt) then
    writeTimestamp pid t

def writeEphemeral (pid : PeerId) (e : List UInt8) : WG.M Unit := do
  setPeer pid { (← getPeer pid) with remoteEphemeral := e }

def writeMaterial (pid : PeerId) (hash ck : List UInt8) (index : Nat) : WG.M Unit := do
  setPeer pid { (← getPeer pid) with hash, chainingKey := ck, remoteIndex := index }

def writeConsumption (pid : PeerId) (time : Int64) : WG.M Unit := do
  setPeer pid { (← getPeer pid) with lastInitiationConsumption := time }

def writeConsumedTag (pid : PeerId) : WG.M Unit := do
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION }

def successWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (timestamp : PeerId → List UInt8 → List UInt8 → m Unit)
    (msg e ckSs hashT t : List UInt8) (peer : Option PeerId) (pid : PeerId)
    (p : Peer) : m (Option PeerId) := do
  let out (peer ret : Option PeerId) := step (Queues.RxCredits.HandshakeLoans.initiationOut peer ret)
  step (writeEphemeral pid e)
  timestamp pid p.latestTimestamp t
  step (writeMaterial pid hashT ckSs (u32le msg 4))
  let consumption ← step (hiddenClock64 .consumptionNow)
  let last := (← step (getPeer pid)).lastInitiationConsumption
  let diff : Int64 := last - consumption
  if ← step (branchCmp .consumeLaterTime (diff < 0) diff.toInt 0) then
    step (writeConsumption pid consumption)
  step (writeConsumedTag pid)
  out peer (some pid)

def checkedWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (timestamp : PeerId → List UInt8 → List UInt8 → m Unit)
    (msg e ckSs hashT t : List UInt8) (peer : Option PeerId) (pid : PeerId)
    (p : Peer) : m (Option PeerId) := do
  let out (peer ret : Option PeerId) := step (Queues.RxCredits.HandshakeLoans.initiationOut peer ret)
  let replay := memcmp t p.latestTimestamp != .gt
  let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
  let now ← step (hiddenClock64 .floodNow)
  if ← step (WG.orM (branch .consumeReplay replay)
      (branchCmp .consumeFlood (floodLhs > now) floodLhs.toInt now.toInt)) then
    return ← out peer none
  successWith step timestamp msg e ckSs hashT t peer pid p

def consumeWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (timestamp : PeerId → List UInt8 → List UInt8 → m Unit)
    (msg : List UInt8) : m (Option PeerId) := do
  let out (peer ret : Option PeerId) := step (Queues.RxCredits.HandshakeLoans.initiationOut peer ret)
  let identity := (← step getDev).staticIdentity
  if ← step (branch .consumeNoIdentity !identity.hasIdentity) then return ← out none none
  let hash := noiseHash (handshakeInitHash ++ identity.staticPublic)
  let e := (msg.drop 8).take 32
  let (ck, hash) ← step (messageEphemeral true e handshakeInitChainingKey hash)
  let es ← step (mixDh true ck identity.staticPrivate e)
  if ← step (branch .consumeEsFailed es.isNone) then return ← out none none
  let some (ck, key) := es | step (invariant "unreachable")
  let st ← step (messageDecrypt ((msg.drop 40).take 48) key hash)
  if ← step (branch .consumeStaticFailed st.isNone) then return ← out none none
  let some (s, hash) := st | step (invariant "unreachable")
  let peer ← step (pubkeyLookup s)
  if ← step (branch .consumeNoPeer peer.isNone) then return ← out none none
  let some pid := peer | step (invariant "unreachable")
  let ss ← step (mixPrecomputedDh ck (← step (getPeer pid)).precomputedStaticStatic)
  if ← step (branch .consumeSsFailed ss.isNone) then return ← out peer none
  let some (ckSs, key) := ss | step (invariant "unreachable")
  let ts ← step (messageDecrypt ((msg.drop 88).take 28) key hash)
  if ← step (branch .consumeTimestampFailed ts.isNone) then return ← out peer none
  let some (t, hashT) := ts | step (invariant "unreachable")
  let p ← step (getPeer pid)
  checkedWith step timestamp msg e ckSs hashT t peer pid p

private theorem bind_if {α β : Type} (c : Prop) [Decidable c] (x y : WG.M α) (f : α → WG.M β) :
    (if c then x else y) >>= f = (if c then x >>= f else y >>= f) := by
  split <;> rfl

theorem consume_factor (msg : List UInt8) :
    consumeWith (fun a => a) timestampStep msg = consumeInitiation msg := by
  simp only [consumeWith, checkedWith, successWith, timestampStep, writeTimestamp, writeEphemeral, writeMaterial,
    writeConsumption, writeConsumedTag, consumeInitiation,
    Queues.RxCredits.HandshakeLoans.initiationOut, bind_assoc, bind_if, pure_bind]
  rfl

end Leanux.Proofs.WG.HandshakeSecurity
