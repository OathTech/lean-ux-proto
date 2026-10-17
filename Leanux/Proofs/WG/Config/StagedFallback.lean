import Leanux.Proofs.WG.Config.StagedFallbackSource
import Leanux.Proofs.WG.Config.KeyReferences

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Decorate the actual absent-key branch. -/
def observedStagedAfterGetNone (pid : PeerId) (packets : List Packet) : WG.M (Int64 × Option Bool) := do
  _ ← branch .stagedNoKeypair true
  observedStagedFallback pid packets none false

/-- Specialized invalid-key prefix. The erasure below states its original domain;
no equivalence outside that domain is asserted. The invalid decision is read from
its actual resident keypair before the fallback. -/
def observedStagedAfterGetInvalid (pid : PeerId) (packets : List Packet) (id : KeypairId) : WG.M (Int64 × Option Bool) := do
  _ ← branch .stagedNoKeypair false
  let k ← getKeypair id
  _ ← branch .stagedKeyInvalid !k.sending.isValid
  observedStagedFallback pid packets (some id) false

theorem observedStagedAfterGetNone_erase (pid : PeerId) (packets : List Packet) :
    (do let _ ← observedStagedAfterGetNone pid packets; pure ()) = stagedAfterGet pid packets none := by
  simp only [observedStagedAfterGetNone, stagedAfterGet, bind_assoc]
  rw [observedStagedFallback_erase]
  simp [branch, AmbientM.branch]

theorem observedStagedAfterGetInvalid_erase (pid : PeerId) (packets : List Packet) (id : KeypairId)
    (d : Device) (k : Keypair) (keyResident : d.keypairs[id]? = some k)
    (invalid : k.sending.isValid = false) (g : WGWorld) (ambient : Ambient)
    (device : g.dev = some d) :
    (((do let _ ← observedStagedAfterGetInvalid pid packets id; pure ()) : WG.M Unit).run g).run ambient =
      ((stagedAfterGet pid packets (some id)).run g).run ambient := by
  have factor : (do let _ ← observedStagedAfterGetInvalid pid packets id; pure ()) = (do
      _ ← branch .stagedNoKeypair false
      let k ← getKeypair id
      _ ← branch .stagedKeyInvalid !k.sending.isValid
      stagedFallback pid packets (some id) false : WG.M Unit) := by
    simp only [observedStagedAfterGetInvalid, bind_assoc, observedStagedFallback_erase]
  rw [factor]
  simp [stagedAfterGet, branch, AmbientM.branch, getKeypair, getDev, device, keyResident, invalid]

/-- Exact packet restoration and queue effect, selected by the actual observed clock and peek. -/
def stagedFallbackObservation (d : Device) (pid : PeerId) (p : Peer) (packets : List Packet)
    (observation : Int64 × Option Bool) (s : Campaign2.Snapshot) : Prop :=
  let restored := {p with staged := packets ++ p.staged}
  let reset := {restored with timerHandshakeAttempts := 0}
  match observation.2 with
  | none => s.wg.device = some (withPeer (withPeer d pid restored) pid reset) ∧
      (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ observation.1 ∨ p.isDead = true)
  | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ observation.1 ∧
      p.isDead = false ∧ s.wg.device = some (fallbackDeviceAfterInspection d pid p packets observation.1 queued)

theorem stagedAfterGet_none (pid : PeerId) (packets : List Packet) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observedStagedAfterGetNone pid packets) (fun s => s.wg.device = some d)
      (stagedFallbackObservation d pid p packets) := by
  have put : Campaign2.Ensures (keypairPut none false) (fun s => s.wg.device = some d)
      (fun _ s => s.wg.device = some d) := by
    intro g ambient result final after device run
    obtain ⟨u, current, inputs, execution, post⟩ := keypairPut_none d g ambient device
    rw [run] at execution
    cases execution
    exact post
  intro g ambient observation final after device run
  change g.dev = some d at device
  change ((observedStagedFallback pid packets none false).run g).run _ = _ at run
  exact stagedFallback_exact pid packets none d d p resident put
    g _ observation final after device run

theorem stagedAfterGet_invalid (pid : PeerId) (packets : List Packet) (id : KeypairId)
    (d : Device) (p : Peer) (k : Keypair)
    (resident : d.peers[pid]? = some p) (keyResident : d.keypairs[id]? = some k)
    (invalid : k.sending.isValid = false) (retained : 1 < k.refcount) :
    Campaign2.Ensures (observedStagedAfterGetInvalid pid packets id) (fun s => s.wg.device = some d)
      (stagedFallbackObservation (withKeypair d id {k with refcount := k.refcount - 1}) pid p packets) := by
  have put : Campaign2.Ensures (keypairPut (some id) false) (fun s => s.wg.device = some d)
      (fun _ s => s.wg.device = some (withKeypair d id {k with refcount := k.refcount - 1})) := by
    intro g ambient result final after device run
    obtain ⟨u, current, inputs, execution, post⟩ := keypairPut_retained id d k keyResident retained g ambient device
    rw [run] at execution
    cases execution
    exact post
  intro g ambient observation final after device run
  change g.dev = some d at device
  simp [observedStagedAfterGetInvalid, branch, AmbientM.branch, getKeypair, getDev, device, keyResident, invalid] at run
  exact stagedFallback_exact pid packets (some id) d
    (withKeypair d id {k with refcount := k.refcount - 1}) p
    (by simpa [withKeypair] using resident) put g _ observation final after device run

/-- Historical prediction retained for pending StagedInvalid and key-peer consumers. -/
def fallbackDevice (d : Device) (pid : PeerId) (p : Peer) (packets : List Packet) (now : Int64) : Device :=
  let restored := { p with staged := packets ++ p.staged }
  let reset := { restored with timerHandshakeAttempts := 0 }
  queuedDevice (withPeer (withPeer d pid restored) pid reset) pid reset now

end Leanux.Proofs.WG.Config
