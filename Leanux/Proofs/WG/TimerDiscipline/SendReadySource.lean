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

theorem sendBuffer_no_endpoint (pid : PeerId) (d : Device) (p : Peer)
    (msg : List UInt8) (records : List HiddenRecord) (w : World)
    (device : w.k.wg = some d) (resident : d.peers[pid]? = some p)
    (endpoint : p.endpoint = none) (present : w.hidden = some records)
    (unarmed : w.allocArmed.contains "sendBufSkb" = false) :
    (sendBufferToPeer pid msg).run w = .ok
      ((), {w with steps := noEndpointSendSteps w.netRxSection w.steps}) := by
  have notArmed : "sendBufSkb" ∉ w.allocArmed := by simpa using unarmed
  simp [notArmed, sendBufferToPeer, hiddenAlloc, AllocSite.info, getPeer, getDev, getK,
    branch, device, resident, endpoint, present, AF_INET, AF_INET6, EAFNOSUPPORT,
    noEndpointSendSteps, StateT.run, Bind.bind, Pure.pure, get, getThe,
    MonadStateOf.get, modify, modifyGet, StateT.bind, StateT.pure, StateT.get,
    MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure]

def initiationSendPrefix (pid : PeerId) (msg : List UInt8) : M (List UInt8) := do
  let packet ← addMacToPacket pid msg
  timersTraversal pid
  timersAnyAuthenticatedPacketSent pid
  let now ← hiddenClock64 .initLastSentAgain
  setPeer pid {(← getPeer pid) with lastSentHandshake := now}
  return packet

theorem initiationSendPrefix_run (pid : PeerId) (d : Device) (p : Peer)
    (msg bytes : List UInt8) (rest : List HiddenRecord) (w : World)
    (device : w.k.wg = some d) (resident : d.peers[pid]? = some p)
    (cookieInvalid : p.cookieIsValid = false) (interval : p.persistentKeepaliveInterval = 0)
    (len : bytes.length = 8)
    (present : w.hidden = some ({site := HiddenSite.initLastSentAgain.info.id, bytes} :: rest)) :
    (initiationSendPrefix pid msg).run w =
      .ok (initiationPacket p msg, {w with
        k := {w.k with wg := some (initiationTailDevice d pid p msg bytes)}
        hidden := some rest
        steps := initiationTailSteps w.netRxSection w.steps}) := by
  have passive : HiddenSite.passive 8 = false := by decide
  have drop : bytes.drop 8 = [] := by simp [← len]
  have take : bytes.take 8 = bytes := by simp [← len]
  simp [initiationSendPrefix, addMacToPacket, WG.andM, timersTraversal, timersAnyAuthenticatedPacketSent,
    delTimer, hiddenClock64, hidden, skipAmbient, noteNetRxStart, HiddenSite.info,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, branch, branchCmp,
    device, resident, cookieInvalid, interval, present, passive, len, drop, take,
    initiationPacket, initiationMacPeer, initiationTailPeer, initiationTailDevice,
    initiationTailSteps, initiationTailClock, Peer.setTimer,
    Functor.discard, Functor.mapConst,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set,
    modify, modifyGet, StateT.bind, StateT.pure, StateT.get, StateT.set,
    MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure, Worker.sectionId, Worker.index]

def initiationTail (pid : PeerId) (msg : List UInt8) : M Unit := do
  let packet ← initiationSendPrefix pid msg
  sendBufferToPeer pid packet
  timersHandshakeInitiated pid

theorem initiationTail_run (pid : PeerId) (d : Device) (p : Peer)
    (msg bytes : List UInt8) (input : RetransmitArmInput) (rest : List HiddenRecord) (w : World)
    (device : w.k.wg = some d) (resident : d.peers[pid]? = some p)
    (cookieInvalid : p.cookieIsValid = false) (interval : p.persistentKeepaliveInterval = 0)
    (endpoint : p.endpoint = none) (running : d.running = true) (alive : p.isDead = false)
    (len : bytes.length = 8) (valid : input.Valid) (mode : w.armRecords = true)
    (unarmed : w.allocArmed.contains "sendBufSkb" = false)
    (present : w.hidden = some ({site := HiddenSite.initLastSentAgain.info.id, bytes} :: input.records rest)) :
    ∃ final, (initiationTail pid msg).run w = .ok ((), final) ∧
      final.k.wg = some {initiationTailDevice d pid p msg bytes with
        peers := (initiationTailDevice d pid p msg bytes).peers.insert pid
          ((initiationTailPeer p msg bytes).setTimer .retransmitHandshake
            (some (input.caller + input.delay.toUInt64)))} ∧
      final.hidden = some rest ∧ final.armRecords = true ∧
      final.jiffiesLast = some input.now ∧
      final.timerUnits = retransmitReadyUnits pid input w.timerUnits ∧
      final.sent = w.sent := by
  let mid := {w with
    k := {w.k with wg := some (initiationTailDevice d pid p msg bytes)}
    hidden := some (input.records rest)
    steps := initiationTailSteps w.netRxSection w.steps}
  have first := initiationSendPrefix_run pid d p msg bytes (input.records rest) w
    device resident cookieInvalid interval len present
  have resident' : (initiationTailDevice d pid p msg bytes).peers[pid]? =
      some (initiationTailPeer p msg bytes) := by simp [initiationTailDevice]
  have send := sendBuffer_no_endpoint pid (initiationTailDevice d pid p msg bytes)
    (initiationTailPeer p msg bytes) (initiationPacket p msg) (input.records rest) mid rfl resident'
    endpoint rfl unarmed
  let beforeArm := {mid with steps := noEndpointSendSteps mid.netRxSection mid.steps}
  have arm := retransmitReady_run pid (initiationTailDevice d pid p msg bytes)
    (initiationTailPeer p msg bytes) input rest resident' running alive valid beforeArm rfl mode rfl
  let final := {beforeArm with
    k := {beforeArm.k with wg := some {initiationTailDevice d pid p msg bytes with
      peers := (initiationTailDevice d pid p msg bytes).peers.insert pid
        ((initiationTailPeer p msg bytes).setTimer .retransmitHandshake (some (input.caller + input.delay.toUInt64)))}}
    hidden := some rest
    steps := retransmitReadySteps beforeArm.netRxSection beforeArm.steps
    jiffiesLast := some input.now
    timerUnits := retransmitReadyUnits pid input beforeArm.timerUnits}
  have run : (initiationTail pid msg).run w = .ok ((), final) := by
    rw [initiationTail, StateT.run_bind, first]
    change ((sendBufferToPeer pid (initiationPacket p msg)).run mid >>= fun out =>
      (timersHandshakeInitiated pid).run out.2) = _
    rw [send]
    exact arm
  exact ⟨_, run, rfl, rfl, mode, rfl, rfl, rfl⟩

end Leanux.Proofs.WG.TimerDiscipline.SendReady

namespace Leanux.Proofs.WG.TimerDiscipline.SendReady
open Leanux Leanux.WG Campaign2 Noise

def initiationEntry (pid : PeerId) : M Bool := do
  if ← branchExpired .initRateLimited (← getPeer pid).lastSentHandshake REKEY_TIMEOUT (!·) then return false
  let now ← hiddenClock64 .initLastSent
  setPeer pid {(← getPeer pid) with lastSentHandshake := now}
  return true

theorem initiationEntry_run (pid : PeerId) (d : Device) (p : Peer)
    (rate last : List UInt8) (rest : List HiddenRecord) (w : World)
    (device : w.k.wg = some d) (resident : d.peers[pid]? = some p)
    (rateLen : rate.length = 8) (lastLen : last.length = 8)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ initiationTailClock rate)
    (present : w.hidden = some ({site := HiddenSite.birthdateExpired.info.id, bytes := rate} ::
      {site := HiddenSite.initLastSent.info.id, bytes := last} :: rest)) :
    (initiationEntry pid).run w = .ok (true, {w with
      k := {w.k with wg := some (initiationEntryDevice d pid p last)}
      hidden := some rest
      steps := w.steps.push {decision := .initRateLimited, outcome := false, operands := some ((p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64).toInt, (initiationTailClock rate).toInt), netRx := w.netRxSection}}) := by
  have passiveRate : HiddenSite.passive 6 = false := by decide
  have passiveLast : HiddenSite.passive 7 = false := by decide
  have rateDrop : rate.drop 8 = [] := by simp [← rateLen]
  have rateTake : rate.take 8 = rate := by simp [← rateLen]
  have lastDrop : last.drop 8 = [] := by simp [← lastLen]
  have lastTake : last.take 8 = last := by simp [← lastLen]
  have expired' : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤
      Int64.ofNat (rate.foldr (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0) := expired
  simp [initiationEntry, branchExpired, birthdateTest, hiddenClock64, hidden, skipAmbient,
    noteNetRxStart, HiddenSite.info, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branchCmp, device, resident, present, passiveRate, passiveLast, rateLen, lastLen,
    rateDrop, rateTake, lastDrop, lastTake, initiationEntryDevice, initiationEntryPeer,
    initiationTailClock, expired', StateT.run, Bind.bind, Pure.pure, get, getThe,
    MonadStateOf.get, set, modify, modifyGet, StateT.bind, StateT.pure, StateT.get,
    StateT.set, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure,
    Worker.sectionId, Worker.index]

def afterEntry (pid : PeerId) : M Unit := do
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
    (run : (createInitiation pid).run w = .ok (some msg, created)) :
    (afterEntry pid).run w = (initiationTail pid msg).run
      {created with steps := created.steps.push {decision := .initCreated, outcome := true, netRx := created.netRxSection}} := by
  rw [afterEntry, StateT.run_bind, run]
  rfl

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
    (w : World) (device : w.k.wg = some d) (mode : w.armRecords = true)
    (unarmed : w.allocArmed.contains "sendBufSkb" = false)
    (present : w.hidden = some ({site := 6, bytes := rate} :: {site := 7, bytes := last} ::
      {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
      Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest))) :
    let made := sendCreationResult pid d p last ephemeral clock fresh.value
    ∃ final, (sendHandshakeInitiation pid).run w = .ok ((), final) ∧
      final.k.wg = some {initiationTailDevice made.2 pid createdPeer made.1 tailClock with
        peers := (initiationTailDevice made.2 pid createdPeer made.1 tailClock).peers.insert pid
          ((initiationTailPeer createdPeer made.1 tailClock).setTimer .retransmitHandshake
            (some (input.caller + input.delay.toUInt64)))} ∧
      final.hidden = some rest ∧ final.armRecords = true ∧ final.jiffiesLast = some input.now := by
  let supplied := {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
    Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest)
  let beforeCreate := {w with
    k := {w.k with wg := some (initiationEntryDevice d pid p last)}
    hidden := some supplied
    steps := w.steps.push {decision := .initRateLimited, outcome := false, operands := some ((p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64).toInt, (initiationTailClock rate).toInt), netRx := w.netRxSection}}
  have entry : (initiationEntry pid).run w = .ok (true, beforeCreate) :=
    initiationEntry_run pid d p rate last supplied w device resident rateLen lastLen expired present
  obtain ⟨msg, created, creationRun, exactMsg, exactDevice, exactRecords, exactMode⟩ :=
    InitiationReady.createInitiation_projected pid (initiationEntryDevice d pid p last)
      (initiationEntryPeer p last) true (by simp [initiationEntryDevice]) identity word nonnull
      ephemeral clock randomWidth width secretNonNull pubOk dhOk collisions fresh
      ({site := 8, bytes := tailClock} :: input.records rest) allCollide isFresh
      beforeCreate ⟨rfl, rfl, mode⟩
  have allocSame := (Noise.ensures_iff _ _ _).mpr
    (createInitiation_allocArmed w.allocArmed pid)
    beforeCreate msg created rfl creationRun
  subst msg
  let made := sendCreationResult pid d p last ephemeral clock fresh.value
  let beforeTail := {created with steps := created.steps.push {decision := .initCreated, outcome := true, netRx := created.netRxSection}}
  obtain ⟨final, tailRun, finalDevice, records, finalMode, now, units, sent⟩ :=
    initiationTail_run pid made.2 createdPeer made.1 tailClock input rest beforeTail
      exactDevice createdResident cookieInvalid interval endpoint running alive tailLen valid exactMode
      (by change created.allocArmed.contains "sendBufSkb" = false; rw [allocSame]; exact unarmed)
      exactRecords
  refine ⟨final, ?_, finalDevice, records, finalMode, now⟩
  rw [sendInitiation_factored, StateT.run_bind, entry]
  change (afterEntry pid).run beforeCreate = .ok ((), final)
  rw [afterEntry_created pid made.1 beforeCreate created creationRun]
  exact tailRun
end Leanux.Proofs.WG.TimerDiscipline.SendReady
