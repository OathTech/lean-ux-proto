import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.TimerDiscipline.SendReadySource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.SendReady
open Leanux Leanux.WG Campaign2 Noise

/-- Retain the actual creation execution and every Product component before
continuing with the current wheel arm. The entry/send prefix changes only the
fields fixed by the checked source cuts. -/
def sendInitiationContinuation (pid : PeerId) (d : Device) (p createdPeer : Peer)
    (rate last ephemeral clock tailClock : List UInt8)
    (collisions : List Index.Draw) (fresh : Index.Draw) (input : RetransmitArmInput)
    (rest : List HiddenRecord) : Leanux.M Unit := do
  let supplied := {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
    Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest)
  modify fun initial => initiationCreationState initial d pid p rate last supplied
  let _ ← liftWG (createInitiation pid)
  let made := sendCreationResult pid d p last ephemeral clock fresh.value
  modify fun created => initiationArmState
    {created with ambient := {created.ambient with
      steps := created.ambient.steps.push {decision := .initCreated, outcome := true, netRx := created.ambient.netRxSection}}}
    made.2 pid createdPeer made.1 tailClock input rest
  liftWG (armTimer pid .retransmitHandshake input.delay (some input.caller))

/-- The original supplied-record domain determines exact outcome agreement
through actual creation and the arm continuation, including wheel-record errors.
No unconditional sender success is asserted. -/
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
    Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.armRecords = true ∧
        s.ambient.allocArmed.contains "sendBufSkb" = false ∧ s.ambient.hidden = some ({site := 6, bytes := rate} :: {site := 7, bytes := last} ::
        {site := 1, bytes := ephemeral} :: {site := 3, bytes := clock} ::
        Index.drawStream collisions fresh ({site := 8, bytes := tailClock} :: input.records rest)))
      (liftWG (sendHandshakeInitiation pid))
      (sendInitiationContinuation pid d p createdPeer rate last ephemeral clock tailClock
        collisions fresh input rest) := by
  intro initial pre
  obtain ⟨created, creation, _, _, _, effect⟩ := sendInitiation_total pid d p resident
    rate last ephemeral clock tailClock rateLen lastLen expired identity word nonnull
    randomWidth width secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh
    createdPeer createdResident cookieInvalid interval endpoint running alive tailLen input valid
    initial pre.1 pre.2.1 pre.2.2.1 pre.2.2.2
  apply congrArg Product.observeResult
  rw [effect]
  change _ = ((liftWG (createInitiation pid)).run _ >>= _)
  rw [creation]
  rfl

end Leanux.Proofs.WG.TimerDiscipline.SendReady
