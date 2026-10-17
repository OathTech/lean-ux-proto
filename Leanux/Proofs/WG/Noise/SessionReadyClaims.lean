import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Noise.SessionReadySource

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Static readiness and supplied successful allocation/clock records establish
success of every realization. The ordered effect is taken from that same run.
Allocation-ID aliases are allowed; this does not assert final key coherence. -/
theorem beginSession_ready_projected (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p)
    (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨
      p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE)
    (alive : p.isDead = false) (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (ready : SessionReady d p counter) (allocation clock : List UInt8)
    (allocWidth : allocation.length = 40) (allocSuccess : allocation.headD 2 = 1)
    (clockWidth : clock.length = 8) (rest : List HiddenRecord) :
    Campaign2.Returns (beginSession pid)
      (fun s => (s.wg.device = some d ∧ s.wg.keypairCounter = counter) ∧
        s.ambient.hidden = some (sessionReadyRecords allocation clock rest) ∧
        s.ambient.allocArmed.contains "kzallocKeypair" = true)
      (fun ok s => ok = true ∧ ∃ final, s.wg.device = some final ∧
        SessionEffect pid d p counter ok final s.wg.keypairCounter) := by
  intro w ambient pre
  obtain ⟨⟨ok, final⟩, after, run, success⟩ := beginSession_returns_ready pid d p counter resident
    accepted alive word hashed ready allocation clock allocWidth allocSuccess clockWidth rest w ambient pre
  obtain ⟨out, device, effect⟩ := beginSession_effect pid d p counter resident w ambient ok final after pre.1 run
  exact ⟨ok, final, after, run, success, out, device, effect⟩

end Leanux.Proofs.WG.Noise
