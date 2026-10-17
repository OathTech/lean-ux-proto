import Leanux.Proofs.WG.TimerDiscipline.SendReadyModel
import Leanux.Proofs.WG.TimerDiscipline.SendReadyFrames
import Leanux.Proofs.WG.Noise.InitiationReadyClaims
import Leanux.Proofs.WG.TimerDiscipline.InitiationArmSource
import Leanux.Proofs.WG.TimerDiscipline.RetransmitReadyClaims
set_option autoImplicit false
set_option pp.structureInstances false
/-! Original entry, creation and send/rearm cuts, including the caller's ignored
no-endpoint send result. The factorization retains both original guards. -/
namespace Leanux.Proofs.WG.TimerDiscipline.SendReady
open Leanux Leanux.WG Campaign2

-- Local variant of campaign 1 Framing.liftWG_bind, retaining actual Product states.
private theorem liftWG_bind_variant {α β : Type} (action : WG.M α) (next : α → WG.M β) :
    liftWG (action >>= next) = (liftWG action >>= fun x => liftWG (next x)) := by
  have lifted {γ : Type} (a : WG.M γ) (entry) :
      (liftWG a).run entry = ((a.run entry.wg).run entry.ambient).map
        (fun ((x, g), ambient) => (x, {entry with wg := g, ambient})) := by
    unfold liftWG StateT.run
    cases a entry.wg entry.ambient <;> rfl
  funext entry
  change (liftWG (action >>= next)).run entry =
    (liftWG action >>= fun x => liftWG (next x)).run entry
  rw [lifted]
  simp only [StateT.run_bind]
  rw [lifted]
  cases actual : (action.run entry.wg).run entry.ambient with
  | error stop => rfl
  | ok out =>
    obtain ⟨⟨value, current⟩, ambient⟩ := out
    simp only [Except.map]
    exact (lifted (next value) {entry with wg := current, ambient}).symm

theorem sendBuffer_no_endpoint (pid : PeerId) (d : Device) (p : Peer)
    (msg : List UInt8) (records : List HiddenRecord) (w : World)
    (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p)
    (endpoint : p.endpoint = none) (present : w.ambient.hidden = some records)
    (unarmed : w.ambient.allocArmed.contains "sendBufSkb" = false) :
    (liftWG (sendBufferToPeer pid msg)).run w = .ok
      ((), {w with ambient := {w.ambient with steps := noEndpointSendSteps w.ambient.netRxSection w.ambient.steps}}) := by
  have notArmed : "sendBufSkb" ∉ w.ambient.allocArmed := by simpa using unarmed
  have ambientLift {α : Type} (action : AmbientM α) :
      (monadLift action : WG.M α) = StateT.lift action := rfl
  simp [liftWG, StateT.lift, ambientLift, notArmed, sendBufferToPeer, hiddenAlloc, AmbientM.hiddenAlloc, AllocSite.info, getPeer, getDev,
    branch, AmbientM.branch, device, resident, endpoint, present, AF_INET, AF_INET6, EAFNOSUPPORT,
    noEndpointSendSteps, StateT.run, Bind.bind, Pure.pure, get, getThe,
    MonadStateOf.get, modify, modifyGet, StateT.bind, StateT.pure, StateT.get,
    MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure]

def initiationSendPrefix (pid : PeerId) (msg : List UInt8) : WG.M (List UInt8) := do
  let packet ← addMacToPacket pid msg
  timersTraversal pid
  timersAnyAuthenticatedPacketSent pid
  let now ← hiddenClock64 .initLastSentAgain
  setPeer pid {(← getPeer pid) with lastSentHandshake := now}
  return packet

/-- Current exact prefix effect, including removal of the send-keepalive wheel entry. -/
theorem initiationSendPrefix_run (pid : PeerId) (d : Device) (p : Peer)
    (msg bytes : List UInt8) (rest : List HiddenRecord) (w : World)
    (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p)
    (cookieInvalid : p.cookieIsValid = false) (interval : p.persistentKeepaliveInterval = 0)
    (len : bytes.length = 8)
    (present : w.ambient.hidden = some ({site := HiddenSite.initLastSentAgain.info.id, bytes} :: rest)) :
    (liftWG (initiationSendPrefix pid msg)).run w =
      .ok (initiationPacket p msg, {w with
        wg := {w.wg with dev := some (initiationTailDevice d pid p msg bytes)}
        ambient := {w.ambient with
          hidden := some rest
          steps := initiationTailSteps w.ambient.netRxSection w.ambient.steps}}) := by
  have passive : HiddenSite.passive 8 = false := by decide
  have drop : bytes.drop 8 = [] := by simp [← len]
  have take : bytes.take 8 = bytes := by simp [← len]
  have ambientLift {α : Type} (action : AmbientM α) :
      (monadLift action : WG.M α) = StateT.lift action := rfl
  simp [liftWG, StateT.lift, ambientLift, initiationSendPrefix, addMacToPacket, WG.andM, timersTraversal, timersAnyAuthenticatedPacketSent,
    delTimer, hiddenClock64, AmbientM.hiddenClock64, AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, HiddenSite.info,
    getPeer, getDev, setPeer, modifyDev, branch, AmbientM.branch, branchCmp, AmbientM.branchCmp,
    device, resident, cookieInvalid, interval, present, passive, len, drop, take,
    initiationPacket, initiationMacPeer, initiationTailPeer, initiationTailDevice,
    initiationTailSteps, initiationTailClock, Peer.setTimer, Peer.setWheel,
    Functor.discard, Functor.mapConst,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set,
    modify, modifyGet, StateT.bind, StateT.pure, StateT.get, StateT.set,
    MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure, Worker.sectionId, Worker.index]

def initiationTail (pid : PeerId) (msg : List UInt8) : WG.M Unit := do
  let packet ← initiationSendPrefix pid msg
  sendBufferToPeer pid packet
  timersHandshakeInitiated pid

/-- Exact recorded-arm entry after MAC, traversal, timer deletion, sender
clock, ignored endpoint send, caller/jitter reads and successful arm guard. -/
def initiationArmState (w : World) (d : Device) (pid : PeerId) (p : Peer)
    (msg bytes : List UInt8) (input : RetransmitArmInput) (rest : List HiddenRecord) : World :=
  {w with
    wg := {w.wg with dev := some (initiationTailDevice d pid p msg bytes)}
    ambient := {w.ambient with
      hidden := some ({site := HiddenSite.modTimerArm.info.id, bytes := input.armData} :: rest)
      steps := retransmitReadySteps w.ambient.netRxSection
        (noEndpointSendSteps w.ambient.netRxSection (initiationTailSteps w.ambient.netRxSection w.ambient.steps))}}

/-- The original domain determines the complete prefix and actual arm-tail outcome.
The old unconditional success assertion omitted wheel record requirements. -/
theorem initiationTail_run (pid : PeerId) (d : Device) (p : Peer)
    (msg bytes : List UInt8) (input : RetransmitArmInput) (rest : List HiddenRecord) (w : World)
    (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p)
    (cookieInvalid : p.cookieIsValid = false) (interval : p.persistentKeepaliveInterval = 0)
    (endpoint : p.endpoint = none) (running : d.running = true) (alive : p.isDead = false)
    (len : bytes.length = 8) (valid : input.Valid) (mode : w.ambient.armRecords = true)
    (unarmed : w.ambient.allocArmed.contains "sendBufSkb" = false)
    (present : w.ambient.hidden = some ({site := HiddenSite.initLastSentAgain.info.id, bytes} :: input.records rest)) :
    (liftWG (initiationTail pid msg)).run w =
      (liftWG (armTimer pid .retransmitHandshake input.delay (some input.caller))).run
        (initiationArmState w d pid p msg bytes input rest) := by
  let mid := {w with
    wg := {w.wg with dev := some (initiationTailDevice d pid p msg bytes)}
    ambient := {w.ambient with
      hidden := some (input.records rest)
      steps := initiationTailSteps w.ambient.netRxSection w.ambient.steps}}
  have first := initiationSendPrefix_run pid d p msg bytes (input.records rest) w
    device resident cookieInvalid interval len present
  have resident' : (initiationTailDevice d pid p msg bytes).peers[pid]? =
      some (initiationTailPeer p msg bytes) := by simp [initiationTailDevice]
  have send := sendBuffer_no_endpoint pid (initiationTailDevice d pid p msg bytes)
    (initiationTailPeer p msg bytes) (initiationPacket p msg) (input.records rest) mid rfl resident'
    endpoint rfl unarmed
  let beforeArm := {mid with ambient := {mid.ambient with
    steps := noEndpointSendSteps mid.ambient.netRxSection mid.ambient.steps}}
  have running' : (initiationTailDevice d pid p msg bytes).running = true := by
    simpa only [initiationTailDevice] using running
  have alive' : (initiationTailPeer p msg bytes).isDead = false := by
    simpa only [initiationTailPeer, initiationMacPeer, Peer.setTimer, Peer.setWheel] using alive
  have device' : beforeArm.wg.dev = some (initiationTailDevice d pid p msg bytes) := rfl
  have mode' : beforeArm.ambient.armRecords = true := mode
  have records' : beforeArm.ambient.hidden = some (input.records rest) := rfl
  have arm := retransmitReady_run pid (initiationTailDevice d pid p msg bytes)
    (initiationTailPeer p msg bytes) input rest resident' running' alive' valid beforeArm device' mode' records'
  rw [initiationTail, liftWG_bind_variant, StateT.run_bind, first]
  change ((liftWG (do
    sendBufferToPeer pid (initiationPacket p msg)
    timersHandshakeInitiated pid)).run mid) = _
  rw [liftWG_bind_variant, StateT.run_bind, send]
  exact arm

end Leanux.Proofs.WG.TimerDiscipline.SendReady

namespace Leanux.Proofs.WG.TimerDiscipline.SendReady
open Leanux Leanux.WG Campaign2 Noise

def initiationEntry (pid : PeerId) : WG.M Bool := do
  if ← branchExpired .initRateLimited (← getPeer pid).lastSentHandshake REKEY_TIMEOUT (!·) then return false
  let now ← hiddenClock64 .initLastSent
  setPeer pid {(← getPeer pid) with lastSentHandshake := now}
  return true

theorem initiationEntry_run (pid : PeerId) (d : Device) (p : Peer)
    (rate last : List UInt8) (rest : List HiddenRecord) (w : World)
    (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p)
    (rateLen : rate.length = 8) (lastLen : last.length = 8)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ initiationTailClock rate)
    (present : w.ambient.hidden = some ({site := HiddenSite.birthdateExpired.info.id, bytes := rate} ::
      {site := HiddenSite.initLastSent.info.id, bytes := last} :: rest)) :
    (liftWG (initiationEntry pid)).run w = .ok (true, {w with
      wg := {w.wg with dev := some (initiationEntryDevice d pid p last)}
      ambient := {w.ambient with
        hidden := some rest
        steps := w.ambient.steps.push {decision := .initRateLimited, outcome := false, operands := some ((p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64).toInt, (initiationTailClock rate).toInt), netRx := w.ambient.netRxSection}}}) := by
  have passiveRate : HiddenSite.passive 6 = false := by decide
  have passiveLast : HiddenSite.passive 7 = false := by decide
  have rateDrop : rate.drop 8 = [] := by simp [← rateLen]
  have rateTake : rate.take 8 = rate := by simp [← rateLen]
  have lastDrop : last.drop 8 = [] := by simp [← lastLen]
  have lastTake : last.take 8 = last := by simp [← lastLen]
  have expired' : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤
      Int64.ofNat (rate.foldr (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0) := expired
  have ambientLift {α : Type} (action : AmbientM α) :
      (monadLift action : WG.M α) = StateT.lift action := rfl
  simp [liftWG, StateT.lift, ambientLift, initiationEntry, branchExpired, birthdateTest, hiddenClock64, AmbientM.hiddenClock64, AmbientM.hidden, AmbientM.skipAmbient,
    AmbientM.noteNetRxStart, HiddenSite.info, getPeer, getDev, setPeer, modifyDev,
    branchCmp, AmbientM.branchCmp, device, resident, present, passiveRate, passiveLast, rateLen, lastLen,
    rateDrop, rateTake, lastDrop, lastTake, initiationEntryDevice, initiationEntryPeer,
    initiationTailClock, expired', StateT.run, Bind.bind, Pure.pure, get, getThe,
    MonadStateOf.get, set, modify, modifyGet, StateT.bind, StateT.pure, StateT.get,
    StateT.set, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure,
    Worker.sectionId, Worker.index]

def afterEntry (pid : PeerId) : WG.M Unit := do
  let created ← createInitiation pid
  if ← branch .initCreated created.isSome then
    let some msg := created | invariant "unreachable"
    initiationTail pid msg

theorem sendInitiation_factored (pid : PeerId) :
    sendHandshakeInitiation pid = (do
      if ← initiationEntry pid then afterEntry pid) := by
  simp only [sendHandshakeInitiation, initiationEntry, afterEntry, initiationTail,
    initiationSendPrefix, bind_assoc, pure_bind]
  congr 1
  funext p
  congr 1
  funext limited
  cases limited <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
  rfl
end Leanux.Proofs.WG.TimerDiscipline.SendReady

namespace Leanux.Proofs.WG.TimerDiscipline.SendReady
open Leanux Leanux.WG Campaign2 Noise

theorem afterEntry_created (pid : PeerId) (msg : List UInt8) (w created : World)
    (run : (liftWG (createInitiation pid)).run w = .ok (some msg, created)) :
    (liftWG (afterEntry pid)).run w = (liftWG (initiationTail pid msg)).run
      {created with ambient := {created.ambient with steps := created.ambient.steps.push {decision := .initCreated, outcome := true, netRx := created.ambient.netRxSection}}} := by
  rw [afterEntry, liftWG_bind_variant, StateT.run_bind, run]
  rfl

end Leanux.Proofs.WG.TimerDiscipline.SendReady

namespace Leanux.Proofs.WG.TimerDiscipline.SendReady
open Leanux Leanux.WG Campaign2 Noise

/-- The actual successful entry prefix, retaining all unmodified Product fields. -/
def initiationCreationState (w : World) (d : Device) (pid : PeerId) (p : Peer)
    (rate last : List UInt8) (records : List HiddenRecord) : World :=
  {w with
    wg := {w.wg with dev := some (initiationEntryDevice d pid p last)}
    ambient := {w.ambient with
      hidden := some records
      steps := w.ambient.steps.push {decision := .initRateLimited, outcome := false, operands := some ((p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64).toInt, (initiationTailClock rate).toInt), netRx := w.ambient.netRxSection}}}

/-- Correct the former unconditional totality claim: the original static and
record premises establish actual entry/creation success, followed by the exact
current arm action. Missing wheel records retain their actual errors. -/
theorem sendInitiation_total (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (rate last ephemeral clock tailClock : List UInt8)
    (rateLen : rate.length = 8) (lastLen : last.length = 8)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ initiationTailClock rate)
    (identity : d.staticIdentity.hasIdentity = true)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : p.precomputedStaticStatic ≠ List.replicate 32 0)
    (randomWidth : ephemeral.length = 32) (width : clock.length = 16)
    (secretNonNull : clamp ephemeral ≠ nullPoint)
    (pubOk : (curve25519 (clamp ephemeral) basePoint).2 = true)
    (dhOk : (curve25519 (clamp ephemeral) p.remoteStatic).2 = true)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false)
    (createdPeer : Peer)
    (createdResident : (sendCreationResult pid d p last ephemeral clock fresh.value).2.peers[pid]? = some createdPeer)
    (cookieInvalid : createdPeer.cookieIsValid = false)
    (interval : createdPeer.persistentKeepaliveInterval = 0)
    (endpoint : createdPeer.endpoint = none)
    (running : (sendCreationResult pid d p last ephemeral clock fresh.value).2.running = true)
    (alive : createdPeer.isDead = false)
    (tailLen : tailClock.length = 8) (input : RetransmitArmInput) (valid : input.Valid)
    (w : World) (device : w.wg.dev = some d) (mode : w.ambient.armRecords = true)
    (unarmed : w.ambient.allocArmed.contains "sendBufSkb" = false)
    (present : w.ambient.hidden = some ({site := 6, bytes := rate} :: {site := 7, bytes := last} ::
      {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
      Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest))) :
    let supplied := {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
      Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest)
    let beforeCreate := initiationCreationState w d pid p rate last supplied
    let made := sendCreationResult pid d p last ephemeral clock fresh.value
    ∃ created,
      (liftWG (createInitiation pid)).run beforeCreate = .ok (some made.1, created) ∧
      created.wg.dev = some made.2 ∧
      created.ambient.hidden = some ({site := 8, bytes := tailClock} :: input.records rest) ∧
      created.ambient.armRecords = true ∧
      (liftWG (sendHandshakeInitiation pid)).run w =
        (liftWG (armTimer pid .retransmitHandshake input.delay (some input.caller))).run
          (initiationArmState
            {created with ambient := {created.ambient with
              steps := created.ambient.steps.push {decision := .initCreated, outcome := true, netRx := created.ambient.netRxSection}}}
            made.2 pid createdPeer made.1 tailClock input rest) := by
  let supplied := {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
    Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest)
  let beforeCreate := initiationCreationState w d pid p rate last supplied
  let made := sendCreationResult pid d p last ephemeral clock fresh.value
  have entry : (liftWG (initiationEntry pid)).run w = .ok (true, beforeCreate) :=
    initiationEntry_run pid d p rate last supplied w device resident rateLen lastLen expired present
  obtain ⟨out, createdG, createdAmbient, creationNative, exactMsg, exactDevice, exactRecords, exactMode⟩ :=
    InitiationReady.createInitiation_projected pid (initiationEntryDevice d pid p last)
      (initiationEntryPeer p last) true (by simp [initiationEntryDevice]) identity word nonnull
      ephemeral clock randomWidth width secretNonNull pubOk dhOk collisions fresh
      ({site := 8, bytes := tailClock} :: input.records rest) allCollide isFresh
      beforeCreate.wg beforeCreate.ambient ⟨rfl, rfl, mode⟩
  have allocSame := createInitiation_allocArmed w.ambient.allocArmed pid beforeCreate.wg
    beforeCreate.ambient (out, createdG) createdAmbient rfl creationNative
  subst out
  let created := {beforeCreate with wg := createdG, ambient := createdAmbient}
  have creationRun : (liftWG (createInitiation pid)).run beforeCreate = .ok (some made.1, created) := by
    change (((createInitiation pid).run beforeCreate.wg).run beforeCreate.ambient >>= _) = _
    rw [creationNative]
    rfl
  have createdDevice : created.wg.dev = some made.2 := exactDevice
  have createdRecords : created.ambient.hidden = some ({site := 8, bytes := tailClock} :: input.records rest) := exactRecords
  have createdMode : created.ambient.armRecords = true := exactMode
  let beforeTail := {created with ambient := {created.ambient with
    steps := created.ambient.steps.push {decision := .initCreated, outcome := true, netRx := created.ambient.netRxSection}}}
  have tailRun := initiationTail_run pid made.2 createdPeer made.1 tailClock input rest beforeTail
    createdDevice createdResident cookieInvalid interval endpoint running alive tailLen valid createdMode
    (by change createdAmbient.allocArmed.contains "sendBufSkb" = false; rw [allocSame]; exact unarmed)
    createdRecords
  refine ⟨created, creationRun, createdDevice, createdRecords, createdMode, ?_⟩
  rw [sendInitiation_factored, liftWG_bind_variant, StateT.run_bind, entry]
  change (liftWG (afterEntry pid)).run beforeCreate = _
  rw [afterEntry_created pid made.1 beforeCreate created creationRun]
  exact tailRun

end Leanux.Proofs.WG.TimerDiscipline.SendReady
