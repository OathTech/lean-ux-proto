import Leanux.Proofs.WG.Config.StagedLeaves

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Historical prediction retained for pending callers; the carried contract below
uses the actual observed clock and queue-inspection result. -/
def invalidStagedDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  fallbackDevice (keyReferenceRoundTrip (clearedStaged d pid p) p.keypairCurrent)
    pid { p with staged := [] } p.staged now

/-- The actual key-acquisition result selects the observed fallback branch. -/
def observedInvalidStagedTail (pid : PeerId) (packets : List Packet)
    (key : Option KeypairId) : WG.M (Int64 × Option Bool) :=
  match key with
  | none => observedStagedAfterGetNone pid packets
  | some id => observedStagedAfterGetInvalid pid packets id

/-- Specialized invalid-current-key observation. Equivalence is asserted only on
its original resident/invalid domain, not on a valid sending key. -/
def observedInvalidStaged (pid : PeerId) : WG.M (Option (Int64 × Option Bool)) := do
  let p ← getPeer pid
  if ← branch .stagedEmpty p.staged.isEmpty then return none
  setPeer pid {p with staged := []}
  let key ← keypairGet p.keypairCurrent
  return some (← observedInvalidStagedTail pid p.staged key)

private theorem invalidStagedTail_contract (pid : PeerId) (d : Device) (p : Peer)
    (invalid : ∀ id k, p.keypairCurrent = some id → d.keypairs[id]? = some k → k.sending.isValid = false)
    (before g : WGWorld) (ambient after : Ambient) (key : Option KeypairId)
    (device : before.dev = some (clearedStaged d pid p))
    (getRun : ((keypairGet p.keypairCurrent).run before).run ambient = .ok ((key, g), after)) :
    (((do let _ ← observedInvalidStagedTail pid p.staged key; pure ()) : WG.M Unit).run g).run after =
      ((stagedAfterGet pid p.staged key).run g).run after ∧
    (∀ observation final last,
      ((observedInvalidStagedTail pid p.staged key).run g).run after = .ok ((observation, final), last) →
      stagedFallbackObservation (keyReferenceRoundTrip (clearedStaged d pid p) p.keypairCurrent)
        pid {p with staged := []} p.staged observation (Campaign2.snapshot final last)) := by
  have noneCase (state : g.dev = some (clearedStaged d pid p))
      (same : keyReferenceRoundTrip (clearedStaged d pid p) p.keypairCurrent = clearedStaged d pid p) :
      (((do let _ ← observedInvalidStagedTail pid p.staged none; pure ()) : WG.M Unit).run g).run after =
        ((stagedAfterGet pid p.staged none).run g).run after ∧
      (∀ observation final last,
        ((observedInvalidStagedTail pid p.staged none).run g).run after = .ok ((observation, final), last) →
        stagedFallbackObservation (keyReferenceRoundTrip (clearedStaged d pid p) p.keypairCurrent)
          pid {p with staged := []} p.staged observation (Campaign2.snapshot final last)) := by
    constructor
    · exact congrArg (fun op : WG.M Unit => (op.run g).run after) (observedStagedAfterGetNone_erase pid p.staged)
    · intro observation final last run
      rw [same]
      exact stagedAfterGet_none pid p.staged (clearedStaged d pid p) {p with staged := []}
        (by simp [clearedStaged, withPeer]) g after observation final last state run
  cases current : p.keypairCurrent with
  | none =>
    rw [current] at getRun
    obtain ⟨value, done, inputs, execution, result, state⟩ := keypairGet_none (clearedStaged d pid p) before ambient device
    rw [getRun] at execution
    cases execution
    cases result
    simpa only [current] using noneCase state (by simp [keyReferenceRoundTrip, current])
  | some id =>
    rw [current] at getRun
    cases found : d.keypairs[id]? with
    | none =>
      exact False.elim (keypairGet_missing id (clearedStaged d pid p) found before ambient key g after device getRun)
    | some k =>
      have acquired := keypairGet_present id (clearedStaged d pid p) k found before ambient key g after device getRun
      by_cases zero : k.refcount = 0
      · simp only [zero, ite_true] at acquired
        obtain ⟨rfl, state⟩ := acquired
        simpa only [current] using noneCase state (by simp [keyReferenceRoundTrip, current, clearedStaged, withPeer, found, zero])
      · simp only [zero, ite_false] at acquired
        obtain ⟨rfl, state⟩ := acquired
        let acquiredDevice := withKeypair (clearedStaged d pid p) id {k with refcount := k.refcount + 1}
        have keyResident : acquiredDevice.keypairs[id]? = some {k with refcount := k.refcount + 1} := by
          simp [acquiredDevice, withKeypair]
        have bad : ({k with refcount := k.refcount + 1} : Keypair).sending.isValid = false := invalid id k current found
        constructor
        · exact observedStagedAfterGetInvalid_erase pid p.staged id acquiredDevice
            {k with refcount := k.refcount + 1} keyResident bad g after state
        · intro observation final last run
          have facts := stagedAfterGet_invalid pid p.staged id acquiredDevice {p with staged := []}
            {k with refcount := k.refcount + 1}
            (by simp [acquiredDevice, withKeypair, clearedStaged, withPeer]) keyResident bad
            (by simp; omega) g after observation final last state run
          simpa [keyReferenceRoundTrip, current, clearedStaged, withPeer, found, zero,
            acquiredDevice, withKeypair] using facts

/-- The specialized observer erases to the actual source on its unchanged invalid-key domain,
including missing-key and reference-overflow Stops. -/
theorem observedInvalidStaged_erase (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (invalid : ∀ id k, p.keypairCurrent = some id → d.keypairs[id]? = some k → k.sending.isValid = false)
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) :
    (((do let _ ← observedInvalidStaged pid; pure ()) : WG.M Unit).run g).run ambient =
      ((sendStagedPackets pid).run g).run ambient := by
  rw [← sendStaged_source]
  by_cases empty : p.staged = []
  · simp [observedInvalidStaged, stagedSource, getPeer, getDev, device, resident, empty,
      branch, AmbientM.branch]
  · have notEmpty : p.staged.isEmpty = false := by cases items : p.staged <;> simp_all
    let prepared := {g with dev := some (clearedStaged d pid p)}
    let marked := {ambient with steps := ambient.steps.push {
      decision := .stagedEmpty, outcome := false, netRx := ambient.netRxSection}}
    simp [observedInvalidStaged, stagedSource, getPeer, getDev, device, resident, empty,
      notEmpty, branch, AmbientM.branch, setPeer, modifyDev, bind_assoc]
    change ((((keypairGet p.keypairCurrent).run prepared).run marked >>= fun ((key, current), inputs) =>
      (((do let _ ← observedInvalidStagedTail pid p.staged key; pure ()) : WG.M Unit).run current).run inputs)) =
      (((keypairGet p.keypairCurrent).run prepared).run marked >>= fun ((key, current), inputs) =>
        ((stagedAfterGet pid p.staged key).run current).run inputs)
    cases acquired : ((keypairGet p.keypairCurrent).run prepared).run marked with
    | error err => rfl
    | ok pair =>
      obtain ⟨⟨key, current⟩, inputs⟩ := pair
      exact (invalidStagedTail_contract pid d p invalid prepared current marked inputs key rfl acquired).1

/-- Empty packets produce no observation; a nonempty invalid-key path records the
actual fallback clock and optional queue-inspection Boolean. -/
def invalidStagedObservation (d : Device) (pid : PeerId) (p : Peer)
    (observation : Option (Int64 × Option Bool)) (s : Campaign2.Snapshot) : Prop :=
  if p.staged = [] then observation = none ∧ s.wg.device = some d
  else ∃ observed, observation = some observed ∧
    stagedFallbackObservation (keyReferenceRoundTrip (clearedStaged d pid p) p.keypairCurrent)
      pid {p with staged := []} p.staged observed s

/-- Semantic correction: the queue effect follows the real peek result, including
an already-pending peer queued again. No readiness premise is added. -/
theorem staged_invalid (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (invalid : ∀ id k, p.keypairCurrent = some id → d.keypairs[id]? = some k → k.sending.isValid = false) :
    Campaign2.Ensures (observedInvalidStaged pid) (fun s => s.wg.device = some d)
      (invalidStagedObservation d pid p) := by
  intro g ambient observation final after device run
  change g.dev = some d at device
  by_cases empty : p.staged = []
  · simp [observedInvalidStaged, getPeer, getDev, device, resident, empty, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    simp [invalidStagedObservation, empty, Campaign2.snapshot, Campaign2.core, device]
  · have notEmpty : p.staged.isEmpty = false := by cases items : p.staged <;> simp_all
    let prepared := {g with dev := some (clearedStaged d pid p)}
    let marked := {ambient with steps := ambient.steps.push {
      decision := .stagedEmpty, outcome := false, netRx := ambient.netRxSection}}
    simp [observedInvalidStaged, getPeer, getDev, device, resident, empty,
      notEmpty, branch, AmbientM.branch, setPeer, modifyDev] at run
    change ((((keypairGet p.keypairCurrent).run prepared).run marked >>= fun ((key, current), inputs) =>
      (((observedInvalidStagedTail pid p.staged key).run current).run inputs >>= fun ((seen, last), ending) =>
        .ok ((some seen, last), ending)))) = .ok ((observation, final), after) at run
    cases acquired : ((keypairGet p.keypairCurrent).run prepared).run marked with
    | error err => rw [acquired] at run; cases run
    | ok pair =>
      obtain ⟨⟨key, current⟩, inputs⟩ := pair
      rw [acquired] at run
      dsimp only [Bind.bind, Except.bind] at run
      cases fallback : ((observedInvalidStagedTail pid p.staged key).run current).run inputs with
      | error err => rw [fallback] at run; cases run
      | ok pair =>
        obtain ⟨⟨seen, last⟩, ending⟩ := pair
        rw [fallback] at run
        cases run
        simp only [invalidStagedObservation, empty, ite_false]
        exact ⟨seen, rfl, (invalidStagedTail_contract pid d p invalid prepared current marked inputs key rfl acquired).2
          seen last ending fallback⟩

end Leanux.Proofs.WG.Config
