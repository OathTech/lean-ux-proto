import Leanux.Proofs.WG.TimerDiscipline.WorkerReadyModel
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource
import Leanux.Proofs.WG.TimerDiscipline.SendReadySource
set_option autoImplicit false
set_option pp.structureInstances false

/-! Exact original operation cuts and total composition. Section start clears
pendingWork as the source does; the full dispatch uses actual selection and dequeue. -/
namespace Leanux.Proofs.WG.TimerDiscipline.WorkerReady
open Leanux Leanux.WG Campaign2 Noise SendReady

theorem retainedPut_run (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (retained : 1 < p.refcount)
    (w : World) (device : w.k.wg = some d) :
    (peerPut (some pid)).run w = .ok ((), {w with
      k := {w.k with wg := some {d with peers := d.peers.insert pid {p with refcount := p.refcount - 1}}}
      steps := retainedPutSteps p.refcount w.netRxSection w.steps}) := by
  have positive : 0 < p.refcount := by omega
  have notOne : p.refcount ≠ 1 := by omega
  have notZero : p.refcount ≠ 0 := by omega
  have notUnder : ¬p.refcount < 1 := by omega
  have notOneB : (p.refcount == 1) = false := by simp [notOne]
  have notZeroB : (p.refcount == 0) = false := by simp [notZero]
  simp [peerPut, requireNotPending, refcountDecAndTest, branch, branchCmp,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, resident, device,
    positive, notUnder, notOneB, notZeroB, retainedPutSteps,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get,
    modify, modifyGet, StateT.bind, StateT.pure, StateT.get, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, Except.pure]

theorem handshakeWorker_total (pid : PeerId) (d : Device) (p : Peer)
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
    (retained : 1 < createdPeer.refcount)
    (tailLen : tailClock.length = 8) (input : RetransmitArmInput) (valid : input.Valid)

    (w : World) (device : w.k.wg = some d) (mode : w.armRecords = true)
    (unarmed : w.allocArmed.contains "sendBufSkb" = false)
    (present : w.hidden = some ({site := 6, bytes := rate} :: {site := 7, bytes := last} ::
      {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
      Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest))) :
    let made := sendCreationResult pid d p last ephemeral clock fresh.value
    let sent := sentDevice made.2 pid createdPeer made.1 tailClock input
    let peer := sentPeer createdPeer made.1 tailClock input
    ∃ final, (handshakeSendWorker pid).run w = .ok ((), final) ∧
      final.k.wg = some {sent with peers := sent.peers.insert pid {peer with refcount := peer.refcount - 1}} ∧
      final.hidden = some rest ∧ final.armRecords = true ∧ final.jiffiesLast = some input.now := by
  obtain ⟨beforePut, sendRun, afterDevice, records, afterMode, now⟩ :=
    sendInitiation_total pid d p resident rate last ephemeral clock tailClock rateLen lastLen expired
      identity word nonnull randomWidth width secretNonNull pubOk dhOk collisions fresh rest
      allCollide isFresh createdPeer createdResident cookieInvalid interval endpoint running alive
      tailLen input valid w device mode unarmed present
  let made := sendCreationResult pid d p last ephemeral clock fresh.value
  let sent := sentDevice made.2 pid createdPeer made.1 tailClock input
  let peer := sentPeer createdPeer made.1 tailClock input
  have put := retainedPut_run pid sent peer (by simp [sent, sentDevice, peer])
    (by simpa [peer, sentPeer, initiationTailPeer, initiationMacPeer, Peer.setTimer] using retained)
    beforePut afterDevice
  let final := {beforePut with
    k := {beforePut.k with wg := some {sent with peers := sent.peers.insert pid {peer with refcount := peer.refcount - 1}}}
    steps := retainedPutSteps peer.refcount beforePut.netRxSection beforePut.steps}
  refine ⟨final, ?_, rfl, records, afterMode, now⟩
  rw [handshakeSendWorker, StateT.run_bind, sendRun]
  exact put

end Leanux.Proofs.WG.TimerDiscipline.WorkerReady

namespace Leanux.Proofs.WG.TimerDiscipline.WorkerReady
open Leanux Leanux.WG Campaign2 Noise SendReady

theorem selection_named_run (pid headPid unit : Nat) (d : Device)
    (head : d.sendWorkQueue.head? = some headPid) (queued : pid ∈ d.sendWorkQueue)
    (start : List UInt8) (len : start.length = 16)
    (address : recordWordOf start 1 = unit) (nonnull : unit ≠ 0)
    (rest : List HiddenRecord) (w : World) (device : w.k.wg = some d)
    (present : w.hidden = some ({site := (HiddenSite.sectionStart .sendWorker).info.id, bytes := start} :: rest))
    (resolved : w.unitPeers.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) =
      some (unit, Worker.sendWorker.index, pid)) :
    sendWorkerSelection.run w = .ok ((some unit, pid), w) := by
  have passive : HiddenSite.passive 40 = false := by decide
  change w.hidden = some ({site := 40, bytes := start} :: rest) at present
  change w.unitPeers.find? (fun e => e.1 == unit && e.2.1 == 0) = some (unit, 0, pid) at resolved
  simp [sendWorkerSelection, getDev, getK, peekUnit, skipAmbient, resolveUnit,
    head, queued, len, address, nonnull, device, present, resolved, passive,
    HiddenSite.info, Worker.sectionId, Worker.index,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set,
    StateT.bind, StateT.pure, StateT.get, StateT.set, Except.bind, Except.pure]
  all_goals simp only [← present]

theorem dequeue_run (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pending : p.handshakePending = true)
    (w : World) (device : w.k.wg = some d) :
    (sendWorkerDequeue pid).run w = .ok ((), {w with
      k := {w.k with wg := some (dequeuedSendDevice d pid p)}}) := by
  simp [sendWorkerDequeue, modifyDev, modifyK, getPeer, getDev, getK, setPeer,
    dequeuedSendDevice, resident, pending, device,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get,
    modify, modifyGet, StateT.bind, StateT.pure, StateT.get, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, Except.pure]

theorem start_run (bytes : List UInt8) (len : bytes.length = 16)
    (rest : List HiddenRecord) (w : World)
    (present : w.hidden = some ({site := (HiddenSite.sectionStart .sendWorker).info.id, bytes} :: rest)) :
    (hidden (.sectionStart .sendWorker)).run w = .ok (bytes,
      {w with hidden := some rest, pendingWork := w.pendingWork.filter (· != Worker.sendWorker.index)}) := by
  have passive : HiddenSite.passive 40 = false := by decide
  have drop : bytes.drop 16 = [] := by simp [← len]
  have take : bytes.take 16 = bytes := by simp [← len]
  simp [hidden, skipAmbient, noteNetRxStart, HiddenSite.info, Worker.sectionId, Worker.index,
    present, passive, len, drop, take,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set, modify, modifyGet,
    StateT.bind, StateT.pure, StateT.get, StateT.set, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, Except.pure]

theorem stop_run (bytes : List UInt8) (len : bytes.length = 8)
    (rest : List HiddenRecord) (w : World)
    (present : w.hidden = some ({site := (HiddenSite.sectionStop .sendWorker).info.id, bytes} :: rest)) :
    (hidden (.sectionStop .sendWorker)).run w = .ok (bytes, {w with hidden := some rest}) := by
  have passive : HiddenSite.passive 41 = false := by decide
  have drop : bytes.drop 8 = [] := by simp [← len]
  have take : bytes.take 8 = bytes := by simp [← len]
  simp [hidden, skipAmbient, noteNetRxStart, HiddenSite.info, Worker.sectionId, Worker.index,
    present, passive, len, drop, take,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set, modify, modifyGet,
    StateT.bind, StateT.pure, StateT.get, StateT.set, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, Except.pure]

end Leanux.Proofs.WG.TimerDiscipline.WorkerReady

namespace Leanux.Proofs.WG.TimerDiscipline.WorkerReady
open Leanux Leanux.WG Campaign2 Noise SendReady

theorem runOneSendWorker_total (pid : PeerId) (d : Device) (p : Peer)
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
    (createdResident : (sendCreationResult pid (dequeuedSendDevice d pid p) {p with handshakePending := false} last ephemeral clock fresh.value).2.peers[pid]? = some createdPeer)
    (cookieInvalid : createdPeer.cookieIsValid = false)
    (interval : createdPeer.persistentKeepaliveInterval = 0)
    (endpoint : createdPeer.endpoint = none)
    (running : (sendCreationResult pid (dequeuedSendDevice d pid p) {p with handshakePending := false} last ephemeral clock fresh.value).2.running = true)
    (alive : createdPeer.isDead = false)
    (retained : 1 < createdPeer.refcount)
    (tailLen : tailClock.length = 8) (input : RetransmitArmInput) (valid : input.Valid)

    (headPid unit : Nat) (head : d.sendWorkQueue.head? = some headPid)
    (queued : pid ∈ d.sendWorkQueue) (pending : p.handshakePending = true)
    (start stop : List UInt8) (startLen : start.length = 16) (stopLen : stop.length = 8)
    (address : recordWordOf start 1 = unit) (nonnullUnit : unit ≠ 0)
    (w : World) (device : w.k.wg = some d) (mode : w.armRecords = true)
    (unarmed : w.allocArmed.contains "sendBufSkb" = false)
    (resolved : w.unitPeers.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) =
      some (unit, Worker.sendWorker.index, pid))
    (present : w.hidden = some ({site := (HiddenSite.sectionStart .sendWorker).info.id, bytes := start} ::
      {site := 6, bytes := rate} :: {site := 7, bytes := last} ::
      {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
      Index.drawStream collisions fresh ({site := 8, bytes := tailClock} ::
        input.records ({site := (HiddenSite.sectionStop .sendWorker).info.id, bytes := stop} :: rest)))) :
    let made := sendCreationResult pid (dequeuedSendDevice d pid p) {p with handshakePending := false}
      last ephemeral clock fresh.value
    let sent := sentDevice made.2 pid createdPeer made.1 tailClock input
    let peer := sentPeer createdPeer made.1 tailClock input
    ∃ final, Env.runOneSendWorker.run w = .ok ((), final) ∧
      final.k.wg = some {sent with peers := sent.peers.insert pid {peer with refcount := peer.refcount - 1}} ∧
      final.hidden = some rest ∧ final.armRecords = true ∧ final.jiffiesLast = some input.now := by
  let stopped := {site := (HiddenSite.sectionStop .sendWorker).info.id, bytes := stop} :: rest
  let bodyRecords := {site := 6, bytes := rate} :: {site := 7, bytes := last} ::
    {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
    Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records stopped)
  have selection := selection_named_run pid headPid unit d head queued start startLen address
    nonnullUnit bodyRecords w device present resolved
  let dequeued := {w with k := {w.k with wg := some (dequeuedSendDevice d pid p)}}
  have dequeue := dequeue_run pid d p resident pending w device
  let beforeBody := {dequeued with hidden := some bodyRecords, pendingWork := dequeued.pendingWork.filter (· != Worker.sendWorker.index)}
  have enter := start_run start startLen bodyRecords dequeued present
  obtain ⟨afterBody, bodyRun, finalDevice, finalRecords, finalMode, finalNow⟩ :=
    handshakeWorker_total pid (dequeuedSendDevice d pid p) {p with handshakePending := false}
      (by simp [dequeuedSendDevice]) rate last ephemeral clock tailClock rateLen lastLen expired
      identity word nonnull randomWidth width secretNonNull pubOk dhOk collisions fresh stopped
      allCollide isFresh createdPeer createdResident cookieInvalid interval endpoint running alive
      retained tailLen input valid beforeBody rfl mode unarmed rfl
  have leave := stop_run stop stopLen rest afterBody finalRecords
  let final := {afterBody with hidden := some rest}
  refine ⟨final, ?_, finalDevice, rfl, finalMode, finalNow⟩
  rw [runOneSendWorker_source, StateT.run_bind, selection]
  change ((sendWorkerDequeue pid).run w >>= fun out =>
    (Env.runWorker .sendWorker (handshakeSendWorker pid)).run out.2) = _
  rw [dequeue]
  change (Env.runWorker .sendWorker (handshakeSendWorker pid)).run dequeued = _
  rw [sendWorkerSection_source, StateT.run_bind, enter]
  change ((handshakeSendWorker pid).run beforeBody >>= fun out =>
    (hidden (.sectionStop .sendWorker)).run out.2 >>= fun last => Except.ok ((), last.2)) = _
  rw [bodyRun]
  change ((hidden (.sectionStop .sendWorker)).run afterBody >>= fun last => Except.ok ((), last.2)) = _
  rw [leave]
  rfl

end Leanux.Proofs.WG.TimerDiscipline.WorkerReady
