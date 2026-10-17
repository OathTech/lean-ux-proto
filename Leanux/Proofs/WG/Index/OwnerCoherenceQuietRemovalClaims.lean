import Leanux.Proofs.WG.Index.OwnerCoherenceQuietRemovalFrames
import Leanux.Proofs.WG.Config.QuietRemoval
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Whole quiet peer removal preserves local owner coherence when every
surviving owner is detached at a last reference. Crypt, NAPI, packet and timer
refusals remain the original source outcomes; no readiness is assumed. -/
theorem peerRemove_quiet_owner_coherent (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (count : 0 < d.numPeers)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)
    (noList : p.allowedipsList = [])
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (detached : LastOwnerDetached d pid p) :
    Campaign2.Ensures (peerRemove (some pid))
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient value final after pre run
  have removal : Config.RemovalEffect (Config.unlistPeer d pid) p.allowedipsList
      (Config.unlistPeer d pid) := by rw [noList]; rfl
  have actual := Config.peerRemove_quiet_returns pid d (Config.unlistPeer d pid) p
    resident live count empty send clear removal g ambient pre.1
  have erased : Config.erasePeerList p.allowedipsList p = p := by
    rw [noList]
    rfl
  rw [erased, run] at actual
  change Config.quietRemovalOutcome (Config.deadPeerDevice (Config.unlistPeer d pid) pid p)
    pid {p with isDead := true} (.ok (value, Campaign2.snapshot final after)) at actual
  have success : ∃ observed,
      (.ok (value, Campaign2.snapshot final after) : Campaign2.Outcome Unit) = .ok ((), observed) ∧
      observed.wg.device = some (Config.quietRemovedDevice
        (Config.deadPeerDevice (Config.unlistPeer d pid) pid p) pid {p with isDead := true}) := by
    unfold Config.quietRemovalOutcome at actual
    dsimp only at actual
    split at actual
    · cases actual
    · split at actual
      · cases actual
      · exact actual
  obtain ⟨observed,equal,device⟩ := success
  have same : Campaign2.snapshot final after = observed := (Prod.mk.inj (Except.ok.inj equal)).2
  rw [← same] at device
  intro current present
  rw [device] at present
  cases present
  exact quietRemovedDead_owner_coherent d pid p resident live noList (pre.2 d pre.1) detached

end Leanux.Proofs.WG.Index
