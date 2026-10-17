import Leanux.Proofs.WG.Index.SessionAliasModel
import Leanux.Proofs.WG.Noise.SessionReadyClaims
import Leanux.Proofs.WG.Index.LookupProvenanceSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

open SessionAliasWitness

/-- The real successful responder rotation puts the just-allocated identity
through the old previous slot, before publishing that identity in the table. -/
private theorem sessionAlias_effect (counter finalCounter : Nat) (final : Device)
    (effect : SessionEffect 0 device peer counter true final finalCounter) :
    final.keypairs[1]? = none ∧ final.indexTable = [published] ∧
      final.nextKeypairId = 2 ∧ finalCounter = counter + 1 := by
  obtain ⟨_, _, _, count, birth, rotated, steps, _, rfl⟩ := effect
  have resultCounter := count
  change RotationRun 0 (sessionPrepared 0 device peer counter birth)
    [.write (.next (some 1)), .put none, .write (.previous none), .put (some 1)] rotated at steps
  cases steps with
  | write start final change p rest resident tail =>
    have same : p = sessionZeroPeer peer := by
      simpa [sessionPrepared, device] using resident.symm
    subst p
    cases tail with
    | put _ middle _ _ _ release tail =>
      cases release
      cases tail with
      | write start final change p rest resident tail =>
        have same : p = RotationWrite.apply (.next (some 1)) (sessionZeroPeer peer) := by
          simpa [rotationWriteDevice] using resident.symm
        subst p
        cases tail with
        | put _ middle _ _ _ release tail =>
          cases release with
          | present d id key resident live word =>
            have ref : key.refcount = 1 := by
              have same := congrArg (Option.map Keypair.refcount) resident
              simpa [rotationWriteDevice,sessionPrepared,sessionDerivedDevice,
                sessionDerivedKey,sessionAssignedKey,createdDevice,device,peer,
                HANDSHAKE_CREATED_RESPONSE,HANDSHAKE_CONSUMED_RESPONSE] using same.symm
            cases tail
            refine ⟨?_, ?_, ?_, resultCounter⟩
            · simp [releasedDevice, ref, unhashKeypair]
            · simp [releasedDevice, ref, unhashKeypair, rotationWriteDevice,
                sessionPrepared,sessionDerivedDevice,createdDevice,device,entry,
                replaceOwner,removeOwner,published]
            · simp [releasedDevice,ref,unhashKeypair,rotationWriteDevice,
                sessionPrepared,sessionDerivedDevice,createdDevice,device]

/-- The original beginSession succeeds on actual allocation/birthdate records,
then leaves a uniquely hashed but absent keypair. Other native/Ambient fields
remain arbitrary; the missing slot invariant is not replaced with readiness. -/
theorem sessionAlias_returns (counter : Nat) :
    Campaign2.Returns (beginSession 0) (input counter)
      (fun ok s => ok = true ∧ ∃ final, s.wg.device = some final ∧
        final.keypairs[1]? = none ∧ final.indexTable = [published] ∧
        final.nextKeypairId = 2 ∧ s.wg.keypairCounter = counter + 1) := by
  have resident : device.peers[0]? = some peer := by simp [device]
  have ready : SessionReady device peer counter := by
    intro id repeated
    simp [rotationReleases,rotationPlan,rotateResponder,
      sessionZeroPeer,peer,HANDSHAKE_CREATED_RESPONSE,HANDSHAKE_CONSUMED_RESPONSE] at repeated
    have same : id = 1 := by simpa using repeated
    subst id
    refine ⟨{internalId := counter + 1,peer := some 0}, ?_, by simp, ?_⟩
    · simp [createdDevice,device,peer]
    · simp [rotationReleases,rotationPlan,rotateResponder,sessionZeroPeer,peer,
        device,HANDSHAKE_CREATED_RESPONSE,HANDSHAKE_CONSUMED_RESPONSE]
  intro g ambient pre
  obtain ⟨ok, final, after, run, success, d, device, effect⟩ :=
    beginSession_ready_projected 0 device peer counter resident (Or.inl rfl) rfl (by simp [peer])
      (by simp [device,entry]) ready allocation clock (by decide) (by decide) (by decide) []
      g ambient ⟨⟨pre.1,pre.2.1⟩,pre.2.2.1,pre.2.2.2⟩
  subst ok
  exact ⟨true,final,after,run,rfl,d,device,sessionAlias_effect counter final.keypairCounter d effect⟩

/-- The actual lookup reaches the published entry and stops when reading its
missing keypair object; it does not return a normal miss or another owner. -/
theorem sessionAlias_lookup_stops (g : WGWorld) (ambient : Ambient) (d : Device)
    (device : g.dev = some d) (table : d.indexTable = [published])
    (absent : d.keypairs[1]? = none) :
    ((indexLookup [.keypair] 7).run g).run ambient =
      .error (.invariant "dangling keypair 1") := by
  obtain ⟨state,middle,next,run,selected,middleDevice⟩ :=
    lookupPrefix_matching [.keypair] 7 (.keypair 1) d
      (by simp [table,published]) (by decide) g ambient device
  rw [indexLookup_factor]
  change (((lookupPrefix [.keypair] 7).run g).run ambient >>= fun ((state,middle),next) =>
    ((lookupFinish state).run middle).run next) = _
  rw [run]
  subst state
  simp [lookupFinish,IndexOwner.peerWord,getKeypair,getDev,middleDevice,absent,
    branch,AmbientM.branch,invariant,AmbientM.invariant]
  rfl


end Leanux.Proofs.WG.Index
