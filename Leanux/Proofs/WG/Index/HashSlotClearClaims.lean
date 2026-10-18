import Leanux.Proofs.WG.Index.HashSlotClearSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

-- Claims
/-- Coverage survives the actual complete clear, including aliased slots.
No residency, reference budget or successful-execution premise is added to the
entry predicate; the conclusion is explicitly about normal returns. -/
theorem keypairsClear_hashSlots (pid : PeerId) :
    Campaign2.Ensures (keypairsClear pid) View.HashSlotsSafe
      (fun _ => View.HashSlotsSafe) := by
  intro g ambient result out after pre run
  obtain ⟨d,p,final,device,_,present,steps,_⟩ :=
    keypairsClear_normal_cuts pid g out ambient after result run
  intro observed found
  have same : observed = final := Option.some.inj (found.symm.trans present)
  subst observed
  exact clearRun_hashSlotCoverage steps (pre d device)

/-- Coherence and hashed-slot coverage discharge final-release detachment
from the same normal clear. The final peer is resident with all three slots
empty; no normal peer release or initialized reachability is asserted. -/
theorem keypairsClear_hashSlots_detached (pid : PeerId) :
    Campaign2.Ensures (keypairsClear pid)
      (fun s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧
        ∃ final p, s.wg.device = some final ∧ final.peers[pid]? = some p ∧
          clearKeys p = [none,none,none] ∧ LastOwnerDetached final pid p) := by
  intro g ambient result out after pre run
  obtain ⟨d,p,final,device,resident,present,steps,peer⟩ :=
    keypairsClear_normal_cuts pid g out ambient after result run
  have coverage := clearRun_hashSlotCoverage steps (pre.1 d device)
  have coherence := clearRun_owner_coherent steps (pre.2 d device)
  have detached := clearRun_hashSlots_detached pid d final p resident steps
    (pre.2 d device) (pre.1 d device)
  refine ⟨?_,?_,final,Config.emptyKeysPeer p,present,peer,rfl,detached⟩
  · intro observed found
    have same : observed = final := Option.some.inj (found.symm.trans present)
    subst observed
    exact coverage
  · intro observed found
    have same : observed = final := Option.some.inj (found.symm.trans present)
    subst observed
    exact coherence


end Leanux.Proofs.WG.Index
