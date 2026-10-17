import Leanux.Proofs.WG.TimerDiscipline.WorkerReadyLeaves
import Leanux.Proofs.WG.TimerDiscipline.SendReadySource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline.WorkerReady
open Leanux Leanux.WG Campaign2 Noise SendReady

-- Local native/Product form of campaign 1 Framing.liftWG_bind.
private theorem liftWG_bind_worker_variant {α β : Type} (action : WG.M α) (next : α → WG.M β) :
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

/-- The original sender domain establishes actual creation, then executes the
current arm and retained-reference release in order. Arm errors stop before put;
this corrects the former unconditional success assertion. -/
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
    (_retained : 1 < createdPeer.refcount)
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
      (liftWG (handshakeSendWorker pid)).run w =
        ((do
          liftWG (armTimer pid .retransmitHandshake input.delay (some input.caller))
          liftWG (peerPut (some pid)) : Leanux.M Unit).run
          (initiationArmState
            {created with ambient := {created.ambient with
              steps := created.ambient.steps.push {decision := .initCreated, outcome := true, netRx := created.ambient.netRxSection}}}
            made.2 pid createdPeer made.1 tailClock input rest)) := by
  obtain ⟨created, creation, exactDevice, exactRecords, exactMode, effect⟩ :=
    sendInitiation_total pid d p resident rate last ephemeral clock tailClock rateLen lastLen expired
      identity word nonnull randomWidth width secretNonNull pubOk dhOk collisions fresh rest
      allCollide isFresh createdPeer createdResident cookieInvalid interval endpoint running alive
      tailLen input valid w device mode unarmed present
  refine ⟨created, creation, exactDevice, exactRecords, exactMode, ?_⟩
  rw [handshakeSendWorker, liftWG_bind_worker_variant, StateT.run_bind, effect]
  rfl

end Leanux.Proofs.WG.TimerDiscipline.WorkerReady

namespace Leanux.Proofs.WG.TimerDiscipline.WorkerReady
open Leanux Leanux.WG Campaign2 Noise SendReady

/-- Exact current dispatch continuation. Dequeue retains residual queue
membership; the original creation premises transport only that pending field.
The actual arm, peer release and section stop retain their errors in order. -/
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
    (start stop : List UInt8) (startLen : start.length = 16) (_stopLen : stop.length = 8)
    (address : recordWordOf start 1 = unit) (nonnullUnit : unit ≠ 0)
    (w : World) (device : w.wg.dev = some d) (mode : w.ambient.armRecords = true)
    (unarmed : w.ambient.allocArmed.contains "sendBufSkb" = false)
    (resolved : w.ambient.unitPeers.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) =
      some (unit, Worker.sendWorker.index, pid))
    (present : w.ambient.hidden = some ({site := (HiddenSite.sectionStart .sendWorker).info.id, bytes := start} ::
      {site := 6, bytes := rate} :: {site := 7, bytes := last} ::
      {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
      Index.drawStream collisions fresh ({site := 8, bytes := tailClock} ::
        input.records ({site := (HiddenSite.sectionStop .sendWorker).info.id, bytes := stop} :: rest)))) :
    let stopped := {site := (HiddenSite.sectionStop .sendWorker).info.id, bytes := stop} :: rest
    let bodyRecords := {site := 6, bytes := rate} :: {site := 7, bytes := last} ::
      {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
      Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records stopped)
    let beforeBody := {w with
      wg := {w.wg with dev := some (dequeuedSendDevice d pid p)}
      ambient := {w.ambient with hidden := some bodyRecords, pendingWork := w.ambient.pendingWork.filter (· != Worker.sendWorker.index)}}
    let actualPeer := {p with handshakePending := (d.sendWorkQueue.erase pid).contains pid}
    let actualCreated := {createdPeer with handshakePending := (d.sendWorkQueue.erase pid).contains pid}
    let supplied := {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
      Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records stopped)
    let beforeCreate := initiationCreationState beforeBody (dequeuedSendDevice d pid p) pid actualPeer rate last supplied
    let made := sendCreationResult pid (dequeuedSendDevice d pid p) actualPeer last ephemeral clock fresh.value
    ∃ created,
      (liftWG (createInitiation pid)).run beforeCreate = .ok (some made.1, created) ∧
      created.wg.dev = some made.2 ∧
      created.ambient.hidden = some ({site := 8, bytes := tailClock} :: input.records stopped) ∧
      created.ambient.armRecords = true ∧
      Env.runOneSendWorker.run w =
        ((do
          liftWG (armTimer pid .retransmitHandshake input.delay (some input.caller))
          liftWG (peerPut (some pid))
          let _ ← hidden (.sectionStop .sendWorker)
          pure () : Leanux.M Unit).run
          (initiationArmState
            {created with ambient := {created.ambient with
              steps := created.ambient.steps.push {decision := .initCreated, outcome := true, netRx := created.ambient.netRxSection}}}
            made.2 pid actualCreated made.1 tailClock input stopped)) := by
  let stopped := {site := (HiddenSite.sectionStop .sendWorker).info.id, bytes := stop} :: rest
  let bodyRecords := {site := 6, bytes := rate} :: {site := 7, bytes := last} ::
    {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
    Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records stopped)
  have selection := selection_named_run pid headPid unit d head queued start startLen address
    nonnullUnit bodyRecords w device present resolved
  let dequeued := {w with wg := {w.wg with dev := some (dequeuedSendDevice d pid p)}}
  have dequeue := dequeue_run pid d p resident pending w device
  let beforeBody := {dequeued with ambient := {dequeued.ambient with
    hidden := some bodyRecords, pendingWork := dequeued.ambient.pendingWork.filter (· != Worker.sendWorker.index)}}
  have enter := start_run start startLen bodyRecords dequeued present
  let actualPeer := {p with handshakePending := (d.sendWorkQueue.erase pid).contains pid}
  let actualCreated := {createdPeer with handshakePending := (d.sendWorkQueue.erase pid).contains pid}
  have actualResident : (sendCreationResult pid (dequeuedSendDevice d pid p) actualPeer
      last ephemeral clock fresh.value).2.peers[pid]? = some actualCreated := by
    have original := createdResident
    simp only [sendCreationResult, initiationEntryDevice, initiationEntryPeer,
      InitiationReady.result, InitiationReady.chainDevice, InitiationReady.secretDevice,
      Std.TreeMap.getElem?_insert_self] at original
    dsimp only [actualCreated, actualPeer]
    rw [← Option.some.inj original]
    simp only [sendCreationResult, initiationEntryDevice, initiationEntryPeer,
      InitiationReady.result, InitiationReady.chainDevice, InitiationReady.secretDevice,
      Std.TreeMap.getElem?_insert_self]
  have actualRunning : (sendCreationResult pid (dequeuedSendDevice d pid p) actualPeer
      last ephemeral clock fresh.value).2.running = true := by
    simpa only [sendCreationResult, initiationEntryDevice, initiationEntryPeer,
      InitiationReady.result, InitiationReady.chainDevice, InitiationReady.secretDevice] using running
  obtain ⟨created, creation, finalDevice, finalRecords, finalMode, bodyRun⟩ :=
    handshakeWorker_total pid (dequeuedSendDevice d pid p) actualPeer
      (by simp [dequeuedSendDevice, actualPeer]) rate last ephemeral clock tailClock rateLen lastLen expired
      identity word nonnull randomWidth width secretNonNull pubOk dhOk collisions fresh stopped
      allCollide isFresh actualCreated actualResident cookieInvalid interval endpoint actualRunning alive
      retained tailLen input valid beforeBody rfl mode unarmed rfl
  refine ⟨created, creation, finalDevice, finalRecords, finalMode, ?_⟩
  rw [runOneSendWorker_source, StateT.run_bind, selection]
  change ((sendWorkerDequeue pid).run w >>= fun out =>
    (Env.runWorker .sendWorker (liftWG (handshakeSendWorker pid))).run out.2) = _
  rw [dequeue]
  change (Env.runWorker .sendWorker (liftWG (handshakeSendWorker pid))).run dequeued = _
  rw [sendWorkerSection_source, StateT.run_bind, enter]
  change ((liftWG (handshakeSendWorker pid)).run beforeBody >>= fun out =>
    (hidden (.sectionStop .sendWorker) : Leanux.M _).run out.2 >>= fun last => Except.ok ((), last.2)) = _
  rw [bodyRun]
  simp only [StateT.run_bind, bind_assoc]
  rfl

end Leanux.Proofs.WG.TimerDiscipline.WorkerReady
