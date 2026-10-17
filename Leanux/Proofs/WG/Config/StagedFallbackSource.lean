import Leanux.Proofs.WG.Config.StagedSource

set_option pp.structureInstances false
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The fallback is decorated only with the actual queue clock and peek result. -/
def observedStagedFallback (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) : WG.M (Int64 × Option Bool) := do
  if invalid then
    let some id := keypair | invariant "unreachable"
    let k ← getKeypair id
    setKeypair id { k with sending := { k.sending with isValid := false } }
  keypairPut keypair false
  for _ in packets do _ ← branch .stagedOrphanWalk true
  _ ← branch .stagedOrphanWalk false
  setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged }
  observedSendQueued pid

theorem observedStagedFallback_erase (pid : PeerId) (packets : List Packet)
    (kp : Option KeypairId) (invalid : Bool) :
    (do let _ ← observedStagedFallback pid packets kp invalid; pure ()) =
      stagedFallback pid packets kp invalid := by
  cases invalid <;> cases kp <;>
    simp only [observedStagedFallback, stagedFallback, Bool.false_eq_true, ite_false, ite_true, bind_assoc, observedSendQueued_erase]

/-- Exact ordered fallback effect indexed by the actual queue inspection. -/
def fallbackDeviceAfterInspection (d : Device) (pid : PeerId) (p : Peer)
    (packets : List Packet) (now : Int64) (queued : Bool) : Device :=
  let restored := { p with staged := packets ++ p.staged }
  let reset := { restored with timerHandshakeAttempts := 0 }
  queuedDeviceAfterInspection (withPeer (withPeer d pid restored) pid reset) pid reset now queued

theorem stagedFallback_exact (pid : PeerId) (packets : List Packet) (kp : Option KeypairId)
    (d afterPut : Device) (p : Peer) (resident : afterPut.peers[pid]? = some p)
    (put : Campaign2.Ensures (keypairPut kp false) (fun s => s.wg.device = some d)
      (fun _ s => s.wg.device = some afterPut)) :
    Campaign2.Ensures (observedStagedFallback pid packets kp false) (fun s => s.wg.device = some d)
      (fun observation s =>
        let restored := { p with staged := packets ++ p.staged }
        let reset := { restored with timerHandshakeAttempts := 0 }
        match observation.2 with
        | none => s.wg.device = some (withPeer (withPeer afterPut pid restored) pid reset) ∧
            (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ observation.1 ∨ p.isDead = true)
        | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ observation.1 ∧
            p.isDead = false ∧ s.wg.device = some (fallbackDeviceAfterInspection afterPut pid p packets observation.1 queued)) := by
  let Q : (Int64 × Option Bool) → WGWorld → Prop := fun observation g =>
    let restored := {p with staged := packets ++ p.staged}
    let reset := {restored with timerHandshakeAttempts := 0}
    match observation.2 with
    | none => g.dev = some (withPeer (withPeer afterPut pid restored) pid reset) ∧
        (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ observation.1 ∨ p.isDead = true)
    | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ observation.1 ∧
        p.isDead = false ∧ g.dev = some (fallbackDeviceAfterInspection afterPut pid p packets observation.1 queued)
  let restored := { p with staged := packets ++ p.staged }
  have walk (items : List Packet) : Ensures
      (forIn items PUnit.unit (fun _ _ => do
        let _ ← branch .stagedOrphanWalk true
        pure (ForInStep.yield PUnit.unit)) : WG.M PUnit)
      (fun g : WGWorld => g.dev = some afterPut) (fun _ g => g.dev = some afterPut) := by
    induction items with
    | nil =>
      intro g ambient result final after device run
      cases run
      exact device
    | cons item rest ih =>
      simp only [List.forIn_cons, bind_assoc]
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (hoare_liftAmbient_variant (AmbientM.branch .stagedOrphanWalk true)
          (fun g : WGWorld => g.dev = some afterPut))) ?_
      intro ignored
      simpa using ih
  have restore : Ensures (do setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged })
      (fun g : WGWorld => g.dev = some afterPut)
      (fun (_ : Unit) g => g.dev = some (withPeer afterPut pid restored)) := by
    intro g ambient result final after device run
    simp [getPeer, getDev, device, resident, setPeer, modifyDev] at run
    rcases run with ⟨rfl, rfl⟩
    rfl
  change Ensures _ (fun g : WGWorld => g.dev = some d) Q
  unfold observedStagedFallback
  simp only [Bool.false_eq_true, ite_false]
  have putNative : Ensures (keypairPut kp false) (fun g : WGWorld => g.dev = some d)
      (fun _ g => g.dev = some afterPut) := put
  refine ensures_bind _ _ putNative ?_
  intro ignored
  refine ensures_bind _ _ (walk packets) ?_
  intro ignored
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.branch .stagedOrphanWalk false)
      (fun g : WGWorld => g.dev = some afterPut))) ?_
  intro ignored
  have factor : (do
      setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged }
      observedSendQueued pid) = ((do
        setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged }) >>= fun _ =>
        observedSendQueued pid) := by simp only [bind_assoc]
  rw [factor]
  refine ensures_bind _ _ restore ?_
  intro ignored
  intro g ambient observation final after device run
  exact sendQueued_exact pid (withPeer afterPut pid restored) restored (by simp [withPeer])
    g ambient observation final after device run

end Leanux.Proofs.WG.Config
