import Leanux.Proofs.WG.Index.RetirementRetentionEffects
import Leanux.Proofs.WG.Index.RetirementReleaseSource
import Leanux.Proofs.WG.Index.HashSlotClearSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise
open Queues.RxCredits

/-- Both ordinary and immediate actual key releases preserve the supplied
retirement obligations on every normal return. Missing/zero-reference failures
remain the original Stops. -/
theorem keypairPut_retirement (retired : Reservations) (key : Option KeypairId)
    (now : Bool) :
    Campaign2.Ensures (keypairPut key now) (View.RetirementSafe retired)
      (fun _ => View.RetirementSafe retired) := by
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
    exact releasedDevice_deadHashedReserved retired d id k now resident (pre d device)

/-- The complete original clear carries retirement across its ordered slot
writes and actual releases. No readiness, alias distinctness, coverage or
coherence assumption is added. -/
theorem keypairsClear_retirement (retired : Reservations) (pid : PeerId) :
    Campaign2.Ensures (keypairsClear pid) (View.RetirementSafe retired)
      (fun _ => View.RetirementSafe retired) := by
  intro g ambient result out after pre run
  obtain ⟨d,p,final,device,_,present,steps,_⟩ :=
    keypairsClear_normal_cuts pid g out ambient after result run
  intro actual found
  change out.dev = some actual at found
  rw [present] at found
  cases found
  exact clearRun_deadHashedReserved steps (pre d device)

/-- Original resident positive-reference peer release retains retirement on
normal returns, including final deletion. This obligation alone needs neither
empty slots nor last-owner detachment. -/
theorem peerPut_retirement (retired : Reservations) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (positive : 0 < p.refcount) :
    Campaign2.Ensures (peerPut (some pid))
      (fun s => s.wg.device = some d ∧ View.RetirementSafe retired s)
      (fun _ => View.RetirementSafe retired) := by
  intro g ambient result out after pre run
  have device := peerPut_normal_device pid d p resident positive
    g out ambient after result pre.1 run
  intro actual found
  change out.dev = some actual at found
  rw [device] at found
  cases found
  exact releasedPeer_deadHashedReserved retired d pid p resident (pre.2 d pre.1)

end Leanux.Proofs.WG.Index
