import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.TimerDiscipline.WorkerReadySource

namespace Leanux.Proofs.WG.TimerDiscipline.WorkerReady
open Leanux Leanux.WG Campaign2 Noise SendReady

/-- Total original named dispatch from initial queue membership and pending flag,
with readiness stated on its deterministic post-dequeue creation result. The
actual section reads and retained reference release belong to this same run. -/
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
    Campaign2.Returns Env.runOneSendWorker
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true ∧
        s.ambient.allocArmed.contains "sendBufSkb" = false ∧
        s.ambient.unitPeers.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) =
          some (unit, Worker.sendWorker.index, pid) ∧
        s.ambient.hidden = some (records start rate last ephemeral clock tailClock stop collisions fresh input rest))
      (fun _ s => s.wg.device = some (result pid d p createdPeer last ephemeral clock tailClock fresh.value input) ∧
        s.ambient.hidden = some rest ∧ s.wg.armRecords = true ∧ s.wg.jiffiesLast = some input.now) := by
  intro w pre
  obtain ⟨final, run, effect⟩ := runOneSendWorker_total pid d p resident rate last ephemeral clock tailClock rateLen lastLen expired identity word
    nonnull randomWidth width secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh
    createdPeer createdResident cookieInvalid interval endpoint running alive retained tailLen input valid
    headPid unit head queued pending start stop startLen stopLen address nonnullUnit
    w pre.1 pre.2.1 pre.2.2.1 pre.2.2.2.1 pre.2.2.2.2
  exact ⟨(), final, run, effect⟩

end Leanux.Proofs.WG.TimerDiscipline.WorkerReady
