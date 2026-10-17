import Leanux.Proofs.WG.Index.SessionLookupSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Positive actual publication-to-lookup handoff under named rotation freshness.
No hidden-record readiness, reference ceiling, or successful-execution premise
is assumed; allocation refusal and every source Stop remain possible. This
local contract does not establish freshness for initialized driver histories. -/
theorem session_lookup_handoff (pid : PeerId) (index : Nat) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (safe : DeviceTablesSafe d)
    (coherent : HashedOwnersCoherent d)
    (handshake : {index, owner := IndexOwner.handshake pid} ∈ d.indexTable)
    (fresh : SessionRotationFresh p d.nextKeypairId) :
    Campaign2.Ensures (sessionThenLookup pid index) (fun s => s.wg.device = some d)
      (fun result s => ∃ final, s.wg.device = some final ∧ DeviceTablesSafe final ∧
        HashedOwnersCoherent final ∧
        (result.1 = false → result.2 = none ∧ final = d) ∧
        (result.1 = true → result.2 = some (.keypair d.nextKeypairId,pid))) := by
  intro g ambient result final after pre run
  exact sessionThenLookup_spec pid index d p resident safe coherent handshake fresh
    g ambient result final after pre run

end Leanux.Proofs.WG.Index
