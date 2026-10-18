import Leanux.Proofs.WG.Index.HashSlotReleaseEffects
import Leanux.Proofs.WG.Index.KeypairReleaseSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Both ordinary and immediate original puts preserve coverage on every normal
return. Missing and zero-reference keys retain their original failure paths. -/
theorem keypairPut_hashSlots (key : Option KeypairId) (now : Bool) :
    Campaign2.Ensures (keypairPut key now) View.HashSlotsSafe
      (fun _ s => View.HashSlotsSafe s) := by
  intro g ambient result out after pre run
  rcases keypairPut_normal_effect key now g out ambient after result run with
    ⟨_,same⟩ | ⟨id,d,k,_,device,resident,_,present⟩
  · intro actual found
    change out.dev = some actual at found
    rw [same] at found
    exact pre actual found
  · intro actual found
    change out.dev = some actual at found
    rw [present] at found
    cases found
    exact releasedDevice_hashSlotCoverage d id k now resident (pre d device)

/-- The actual peer put preserves coverage under the last-release empty-slot
condition. Original queue/timer refusals remain outside the normal postcondition. -/
theorem peerPut_hashSlots (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (empty : p.refcount = 1 → clearKeys p = [none,none,none]) :
    Campaign2.Ensures (peerPut (some pid))
      (fun s => s.wg.device = some d ∧ View.HashSlotsSafe s)
      (fun _ s => View.HashSlotsSafe s) := by
  intro g ambient result out after pre run
  have exactOutcome := peerPut_exact pid d p resident live g ambient pre.1
  change (match peerReleaseRefusal pid p with
    | some stop => Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .error stop
    | none => ∃ final,
        Campaign2.observeResult (((peerPut (some pid)).run g).run ambient) = .ok ((),final) ∧
        final.wg.device = some (releasedPeerDevice d pid p)) at exactOutcome
  rw [run] at exactOutcome
  cases refusal : peerReleaseRefusal pid p with
  | some stop =>
    simp [refusal,Campaign2.observeResult,Except.map] at exactOutcome
  | none =>
    simp only [refusal,Campaign2.observeResult,Except.map,Except.ok.injEq,
      Prod.mk.injEq] at exactOutcome
    obtain ⟨final,⟨_,equal⟩,device⟩ := exactOutcome
    subst final
    intro actual found
    rw [device] at found
    cases found
    exact releasedPeer_hashSlotCoverage d pid p resident empty (pre.2 d pre.1)

end Leanux.Proofs.WG.Index
