import Leanux.Proofs.WG.Index.OwnerCoherenceZeroWorkerFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseClaims
import Leanux.Proofs.WG.Noise.ClearSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- The actual zero-key work item preserves local owner coherence under
last-reference slot coverage. NULL embedded words, insufficient aliased-key
references and final packet/timer refusals retain their original stopped paths.
No work-queue, allowed-IP-list or readiness assumption is added. -/
theorem queuedExpiredZeroKeyMaterial_owner_coherent (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (covered : LastOwnerCovered d pid p) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid)
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient value final after pre run
  let safe := fun state : WGWorld => ∀ current, state.dev = some current → HashedOwnersCoherent current
  have head : Ensures (handshakeClear pid) (fun state => state.dev = some d)
      (fun _ state => state.dev = some (Config.expiryZeroDevice d pid p)) := by
    simpa only [Config.expiryReadPrefix,requireNotPending,pure_bind] using
      Config.expiryReadPrefix_exact pid d p resident
  let zero := Config.expiryZeroDevice d pid p
  let zeroPeer := Config.zeroedHandshake p
  have zeroResident : zero.peers[pid]? = some zeroPeer := by
    simp [zero,zeroPeer,Config.expiryZeroDevice,Config.withPeer]
  have zeroSafe := expiryZeroDevice_owner_coherent d pid p resident (pre.2 d pre.1)
  have zeroCovered := expiryZeroDevice_lastOwnerCovered d pid p covered
  have clear : Ensures (keypairsClear pid) (fun state => state.dev = some zero)
      (fun _ state => ∃ cleared, state.dev = some cleared ∧
        ClearRun pid zero [.next,.previous,.current] cleared ∧
        cleared.peers[pid]? = some (Config.emptyKeysPeer zeroPeer)) := by
    intro state input result out tail device execution
    obtain ⟨cleared,present,steps⟩ := keypairsClear_effect pid zero zeroPeer zeroResident
      state input result out tail device execution
    have peer := keypairsClear_peer pid zeroPeer state input result out tail
      (by simp [peerAt,device,zeroResident]) execution
    refine ⟨cleared,present,steps,?_⟩
    simpa [peerAt,present,Config.emptyKeysPeer] using peer
  have whole : Ensures (queuedExpiredZeroKeyMaterial pid) (fun state => state.dev = some d)
      (fun _ state => safe state) := by
    unfold queuedExpiredZeroKeyMaterial
    refine ensures_bind _ _ head ?_
    intro _
    refine ensures_bind _ _ clear ?_
    intro _ state input result out tail post execution
    obtain ⟨cleared,present,steps,found⟩ := post
    have coherent := clearRun_owner_coherent steps zeroSafe
    have detached := clearRun_covered_detached pid zero cleared zeroPeer zeroResident steps zeroCovered
    have currentSafe : View.OwnerCoherentSafe (Campaign2.snapshot state input) := by
      intro current device
      change state.dev = some current at device
      rw [present] at device
      cases device
      exact coherent
    exact peerPut_owner_coherent pid cleared (Config.emptyKeysPeer zeroPeer) found live detached
      state input result out tail ⟨present,currentSafe⟩ execution
  exact whole g ambient value final after pre.1 run

end Leanux.Proofs.WG.Index
