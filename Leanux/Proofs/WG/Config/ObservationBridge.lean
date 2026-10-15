import Leanux.Proofs.WG.Config.SourceClaims
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Clock observations execute the actual prefix on a copy of the same entry
state, then run the original operation. The copy is never reconstructed from a
projection, and every internal bind keeps its concrete intermediate state. -/
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

def expiryClockRead (pid : PeerId) : M (Campaign2.Snapshot × Int64) := do
  expiryReadPrefix pid
  let before ← Campaign2.read
  let now ← hiddenClock64 .resetLastSent
  pure (before, now)

def queuedClockRead (pid : PeerId) : M (Peer × Campaign2.Snapshot × Int64) := do
  let peer ← queuedReadPrefix pid
  let before ← Campaign2.read
  let now ← hiddenClock64 .birthdateExpired
  pure (peer, before, now)

def observedExpiry (pid : PeerId) : M (Campaign2.Outcome (Campaign2.Snapshot × Int64)) := do
  let observation ← Campaign2.inspect (expiryClockRead pid)
  expireCurrentPeerKeypairs pid
  pure observation

def observedQueuedHandshake (pid : PeerId) : M (Campaign2.Outcome (Peer × Campaign2.Snapshot × Int64)) := do
  let observation ← Campaign2.inspect (queuedClockRead pid)
  sendQueuedHandshakeInitiation pid false
  pure observation

/-- Discarding the observation executes precisely the original operation,
including its error outcome. Inspection cannot introduce an extra failure. -/
theorem observedExpiry_erase (pid : PeerId) :
    (do let _ ← observedExpiry pid; pure ()) = expireCurrentPeerKeypairs pid := by
  funext w
  change (((expireCurrentPeerKeypairs pid).run w >>= fun out =>
    Except.ok (Campaign2.observeResult ((expiryClockRead pid).run w), out.2)) >>= fun out =>
      Except.ok ((), out.2)) = (expireCurrentPeerKeypairs pid).run w
  cases h : (expireCurrentPeerKeypairs pid).run w with
  | error e => rfl
  | ok pair => obtain ⟨u, final⟩ := pair; cases u; rfl

/-- The queued-call decoration also erases to the complete original action. -/
theorem observedQueuedHandshake_erase (pid : PeerId) :
    (do let _ ← observedQueuedHandshake pid; pure ()) = sendQueuedHandshakeInitiation pid false := by
  funext w
  change (((sendQueuedHandshakeInitiation pid false).run w >>= fun out =>
    Except.ok (Campaign2.observeResult ((queuedClockRead pid).run w), out.2)) >>= fun out =>
      Except.ok ((), out.2)) = (sendQueuedHandshakeInitiation pid false).run w
  cases h : (sendQueuedHandshakeInitiation pid false).run w with
  | error e => rfl
  | ok pair => obtain ⟨u, final⟩ := pair; cases u; rfl

/-- The concrete source bridge for the decorated expiry computation. -/
theorem observedExpiry_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observedExpiry pid) (fun s => s.wg.device = some d)
      (fun observation final => ∃ now before after,
        observation = .ok ((before, now), after) ∧
        final.wg.device = some (expiredDevice d pid p now)) := by
  intro w observation v hp hr
  change ((expireCurrentPeerKeypairs pid).run w >>= fun out =>
    Except.ok (Campaign2.observeResult ((expiryClockRead pid).run w), out.2)) =
      Except.ok (observation, v) at hr
  cases hrun : (expireCurrentPeerKeypairs pid).run w with
  | error e => rw [hrun] at hr; cases hr
  | ok pair =>
    obtain ⟨u, final⟩ := pair
    cases u
    rw [hrun] at hr
    have hpair := Except.ok.inj hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    obtain ⟨now, before, after, hprefix, hclock, device⟩ :=
      SourceClaims.original_expiry_clock_relation pid d p resident w final hp hrun
    refine ⟨now, Campaign2.snapshot before, Campaign2.snapshot after, ?_, device⟩
    have hread : (expiryClockRead pid).run w =
        .ok ((Campaign2.snapshot before, now), after) := by
      simp only [expiryClockRead, StateT.run_bind, hprefix]
      change ((hiddenClock64 .resetLastSent).run before >>= fun out =>
        Except.ok ((Campaign2.snapshot before, out.1), out.2)) = _
      rw [hclock]
      rfl
    rw [hread]
    rfl

/-- The concrete source bridge for the decorated queue computation. -/
theorem observedQueuedHandshake_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observedQueuedHandshake pid) (fun s => s.wg.device = some d)
      (fun observation final => ∃ now before after,
        observation = .ok (({ p with timerHandshakeAttempts := 0 }, before, now), after) ∧
        final.wg.device = some (queuedDevice (withPeer d pid { p with timerHandshakeAttempts := 0 })
          pid { p with timerHandshakeAttempts := 0 } now)) := by
  intro w observation v hp hr
  change ((sendQueuedHandshakeInitiation pid false).run w >>= fun out =>
    Except.ok (Campaign2.observeResult ((queuedClockRead pid).run w), out.2)) =
      Except.ok (observation, v) at hr
  cases hrun : (sendQueuedHandshakeInitiation pid false).run w with
  | error e => rw [hrun] at hr; cases hr
  | ok pair =>
    obtain ⟨u, final⟩ := pair
    cases u
    rw [hrun] at hr
    have hpair := Except.ok.inj hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    obtain ⟨now, before, after, hprefix, hclock, device⟩ :=
      SourceClaims.original_queued_handshake_clock pid d p resident w final hp hrun
    refine ⟨now, Campaign2.snapshot before, Campaign2.snapshot after, ?_, device⟩
    have hread : (queuedClockRead pid).run w =
        .ok (({ p with timerHandshakeAttempts := 0 }, Campaign2.snapshot before, now), after) := by
      simp only [queuedClockRead, StateT.run_bind, hprefix]
      change ((hiddenClock64 .birthdateExpired).run before >>= fun out =>
        Except.ok (({ p with timerHandshakeAttempts := 0 }, Campaign2.snapshot before, out.1), out.2)) = _
      rw [hclock]
      rfl
    rw [hread]
    rfl

end Leanux.Proofs.WG.Config
