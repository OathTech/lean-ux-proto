import Leanux.Proofs.WG.Config.SourceClaims
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Clock observations execute the actual prefix on a copy of the same entry
state, then run the original operation. The copy is never reconstructed from a
projection, and every internal bind keeps its concrete intermediate state. -/
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

def expiryClockRead (pid : PeerId) : Leanux.M (Campaign2.Product.Snapshot × Int64) := do
  liftWG (expiryReadPrefix pid)
  let before ← Campaign2.Product.read
  let now ← liftWG (hiddenClock64 .resetLastSent : WG.M Int64)
  pure (before, now)

def queuedClockRead (pid : PeerId) : Leanux.M (Peer × Campaign2.Product.Snapshot × Int64) := do
  let peer ← liftWG (queuedReadPrefix pid)
  let before ← Campaign2.Product.read
  let now ← liftWG (hiddenClock64 .birthdateExpired : WG.M Int64)
  pure (peer, before, now)

def observedExpiry (pid : PeerId) : Leanux.M (Campaign2.Product.Outcome (Campaign2.Product.Snapshot × Int64)) := do
  let observation ← Campaign2.Product.inspect (expiryClockRead pid)
  liftWG (expireCurrentPeerKeypairs pid)
  pure observation

def observedQueuedHandshake (pid : PeerId) : Leanux.M (Campaign2.Product.Outcome (Peer × Campaign2.Product.Snapshot × Int64)) := do
  let observation ← Campaign2.Product.inspect (queuedClockRead pid)
  liftWG (sendQueuedHandshakeInitiation pid false)
  pure observation

/-- Discarding the observation executes precisely the original operation,
including its error outcome. Inspection cannot introduce an extra failure. -/
theorem observedExpiry_erase (pid : PeerId) :
    (do let _ ← observedExpiry pid; pure ()) = liftWG (expireCurrentPeerKeypairs pid) := by
  funext w
  change (((liftWG (expireCurrentPeerKeypairs pid)).run w >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((expiryClockRead pid).run w), out.2)) >>= fun out =>
      Except.ok ((), out.2)) = (liftWG (expireCurrentPeerKeypairs pid)).run w
  cases h : (liftWG (expireCurrentPeerKeypairs pid)).run w with
  | error e => rfl
  | ok pair => obtain ⟨u, final⟩ := pair; cases u; rfl

/-- The queued-call decoration also erases to the complete original action. -/
theorem observedQueuedHandshake_erase (pid : PeerId) :
    (do let _ ← observedQueuedHandshake pid; pure ()) = liftWG (sendQueuedHandshakeInitiation pid false) := by
  funext w
  change (((liftWG (sendQueuedHandshakeInitiation pid false)).run w >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((queuedClockRead pid).run w), out.2)) >>= fun out =>
      Except.ok ((), out.2)) = (liftWG (sendQueuedHandshakeInitiation pid false)).run w
  cases h : (liftWG (sendQueuedHandshakeInitiation pid false)).run w with
  | error e => rfl
  | ok pair => obtain ⟨u, final⟩ := pair; cases u; rfl

/-- The concrete source bridge for the decorated expiry computation. -/
theorem observedExpiry_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Product.Ensures (observedExpiry pid) (fun s => s.wg.device = some d)
      (fun observation final => ∃ now before after,
        observation = .ok ((before, now), after) ∧
        final.wg.device = some (expiredDevice d pid p now)) := by
  intro w observation v hp hr
  change ((liftWG (expireCurrentPeerKeypairs pid)).run w >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((expiryClockRead pid).run w), out.2)) =
      Except.ok (observation, v) at hr
  cases hrun : (liftWG (expireCurrentPeerKeypairs pid)).run w with
  | error e => rw [hrun] at hr; cases hr
  | ok pair =>
    obtain ⟨u, final⟩ := pair
    cases u
    rw [hrun] at hr
    have hpair := Except.ok.inj hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    obtain ⟨now, before, after, hprefix, hclock, device⟩ :=
      SourceClaims.original_expiry_clock_relation pid d p resident w final hp hrun
    refine ⟨now, Campaign2.Product.snapshot before, Campaign2.Product.snapshot after, ?_, device⟩
    have hread : (expiryClockRead pid).run w =
        .ok ((Campaign2.Product.snapshot before, now), after) := by
      simp only [expiryClockRead, StateT.run_bind, hprefix]
      change ((liftWG (hiddenClock64 .resetLastSent : WG.M Int64)).run before >>= fun out =>
        Except.ok ((Campaign2.Product.snapshot before, out.1), out.2)) = _
      rw [hclock]
      rfl
    rw [hread]
    rfl

/-- The corrected queue consequence uses its actual inspection-dependent effect.
The clock observation still retains the full Product prefix and read states. -/
theorem observedQueuedHandshake_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Product.Ensures (observedQueuedHandshake pid) (fun s => s.wg.device = some d)
      (fun observation final => ∃ now seen before after,
        observation = .ok (({ p with timerHandshakeAttempts := 0 }, before, now), after) ∧
        match seen with
        | none => final.wg.device = some (withPeer d pid {p with timerHandshakeAttempts := 0}) ∧
            (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∨ p.isDead = true)
        | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∧
            p.isDead = false ∧ final.wg.device = some (queuedDeviceAfterInspection
              (withPeer d pid {p with timerHandshakeAttempts := 0})
              pid {p with timerHandshakeAttempts := 0} now queued)) := by
  intro w observation v hp hr
  change ((liftWG (sendQueuedHandshakeInitiation pid false)).run w >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((queuedClockRead pid).run w), out.2)) =
      Except.ok (observation, v) at hr
  cases hrun : (liftWG (sendQueuedHandshakeInitiation pid false)).run w with
  | error e => rw [hrun] at hr; cases hr
  | ok pair =>
    obtain ⟨u, final⟩ := pair
    cases u
    rw [hrun] at hr
    have hpair := Except.ok.inj hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    obtain ⟨now, seen, before, after, hprefix, hclock, _actualQueue, device⟩ :=
      SourceClaims.original_queued_handshake_clock pid d p resident w final hp hrun
    refine ⟨now, seen, Campaign2.Product.snapshot before, Campaign2.Product.snapshot after, ?_, device⟩
    have hread : (queuedClockRead pid).run w =
        .ok (({ p with timerHandshakeAttempts := 0 }, Campaign2.Product.snapshot before, now), after) := by
      simp only [queuedClockRead, StateT.run_bind, hprefix]
      change ((liftWG (hiddenClock64 .birthdateExpired : WG.M Int64)).run before >>= fun out =>
        Except.ok (({ p with timerHandshakeAttempts := 0 }, Campaign2.Product.snapshot before, out.1), out.2)) = _
      rw [hclock]
      rfl
    rw [hread]
    rfl

end Leanux.Proofs.WG.Config
