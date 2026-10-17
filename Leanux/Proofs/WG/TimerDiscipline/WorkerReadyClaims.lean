import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.TimerDiscipline.WorkerReadySource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.WorkerReady
open Leanux Leanux.WG Campaign2 Noise SendReady

/-- Execute the exact selected/dequeued section prefix, then actual creation,
arm, reference release and section stop. All untouched Product fields come
from that same execution; duplicate queue membership determines pending. -/
def runOneSendWorkerContinuation (pid : PeerId) (d : Device) (p createdPeer : Peer)
    (rate last ephemeral clock tailClock stop : List UInt8)
    (collisions : List Index.Draw) (fresh : Index.Draw) (input : RetransmitArmInput)
    (rest : List HiddenRecord) : Leanux.M Unit := do
  let stopped := {site := (HiddenSite.sectionStop .sendWorker).info.id, bytes := stop} :: rest
  let supplied := {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
    Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records stopped)
  let bodyRecords := {site := 6, bytes := rate} :: {site := 7, bytes := last} :: supplied
  let actualPeer := {p with handshakePending := (d.sendWorkQueue.erase pid).contains pid}
  let actualCreated := {createdPeer with handshakePending := (d.sendWorkQueue.erase pid).contains pid}
  modify fun initial => {initial with
    wg := {initial.wg with dev := some (dequeuedSendDevice d pid p)}
    ambient := {initial.ambient with hidden := some bodyRecords, pendingWork := initial.ambient.pendingWork.filter (· != Worker.sendWorker.index)}}
  modify fun beforeBody => initiationCreationState beforeBody (dequeuedSendDevice d pid p) pid actualPeer rate last supplied
  let _ ← liftWG (createInitiation pid)
  let made := sendCreationResult pid (dequeuedSendDevice d pid p) actualPeer last ephemeral clock fresh.value
  modify fun created => initiationArmState
    {created with ambient := {created.ambient with
      steps := created.ambient.steps.push {decision := .initCreated, outcome := true, netRx := created.ambient.netRxSection}}}
    made.2 pid actualCreated made.1 tailClock input stopped
  liftWG (armTimer pid .retransmitHandshake input.delay (some input.caller))
  liftWG (peerPut (some pid))
  let _ ← hidden (.sectionStop .sendWorker)
  pure ()

/-- Corrected exact Product outcome agreement on the original named-dispatch
domain. Residual queue membership and all arm/release/section errors are kept;
the old record premises do not establish unconditional completion. -/
theorem runOneSendWorker_projected (pid : PeerId) (d : Device) (p : Peer)
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
    (address : recordWordOf start 1 = unit) (nonnullUnit : unit ≠ 0) :
    Campaign2.Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true ∧
        s.ambient.allocArmed.contains "sendBufSkb" = false ∧
        s.ambient.unitPeers.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) =
          some (unit, Worker.sendWorker.index, pid) ∧
        s.ambient.hidden = some (records start rate last ephemeral clock tailClock stop collisions fresh input rest))
      Env.runOneSendWorker
      (runOneSendWorkerContinuation pid d p createdPeer rate last ephemeral clock tailClock stop
        collisions fresh input rest) := by
  intro initial pre
  obtain ⟨created, creation, _, _, _, effect⟩ := runOneSendWorker_total pid d p resident
    rate last ephemeral clock tailClock rateLen lastLen expired identity word nonnull
    randomWidth width secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh
    createdPeer createdResident cookieInvalid interval endpoint running alive retained tailLen input valid
    headPid unit head queued pending start stop startLen stopLen address nonnullUnit
    initial pre.1 pre.2.1 pre.2.2.1 pre.2.2.2.1 pre.2.2.2.2
  apply congrArg Campaign2.Product.observeResult
  rw [effect]
  change _ = ((liftWG (createInitiation pid)).run _ >>= _)
  rw [creation]
  rfl

end Leanux.Proofs.WG.TimerDiscipline.WorkerReady
