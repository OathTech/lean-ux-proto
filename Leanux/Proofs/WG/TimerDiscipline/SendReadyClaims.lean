import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.TimerDiscipline.SendReadySource

namespace Leanux.Proofs.WG.TimerDiscipline.SendReady
open Leanux Leanux.WG Campaign2 Noise

/-- Total original initiation send and retransmit arm from supplied records and
static pure-state readiness. No endpoint means no packet is emitted by the
send-buffer cut; its error is ignored by the original caller, which still arms
the timer. The claim records Device, hidden suffix, mode and final clock. -/
theorem sendInitiation_projected (pid : PeerId) (d : Device) (p : Peer)
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
    (tailLen : tailClock.length = 8) (input : RetransmitArmInput) (valid : input.Valid) :
    Campaign2.Returns (sendHandshakeInitiation pid)
      (fun s => s.wg.device = some d ∧ s.wg.armRecords = true ∧
        s.ambient.allocArmed.contains "sendBufSkb" = false ∧ s.ambient.hidden = some ({site := 6, bytes := rate} :: {site := 7, bytes := last} ::
        {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
        Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest)))
      (fun _ s =>
        let made := sendCreationResult pid d p last ephemeral clock fresh.value
        s.wg.device = some {initiationTailDevice made.2 pid createdPeer made.1 tailClock with
          peers := (initiationTailDevice made.2 pid createdPeer made.1 tailClock).peers.insert pid
            ((initiationTailPeer createdPeer made.1 tailClock).setTimer .retransmitHandshake
              (some (input.caller + input.delay.toUInt64)))} ∧
        s.ambient.hidden = some rest ∧ s.wg.armRecords = true ∧ s.wg.jiffiesLast = some input.now) := by
  intro w pre
  obtain ⟨final, run, post⟩ := sendInitiation_total pid d p resident rate last ephemeral clock tailClock rateLen lastLen expired identity
    word nonnull randomWidth width secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh
    createdPeer createdResident cookieInvalid interval endpoint running alive tailLen input valid
    w pre.1 pre.2.1 pre.2.2.1 pre.2.2.2
  exact ⟨(), final, run, post⟩

end Leanux.Proofs.WG.TimerDiscipline.SendReady
