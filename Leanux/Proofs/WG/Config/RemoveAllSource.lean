import Leanux.Proofs.WG.Config.RemoveAllEffects
import Leanux.Proofs.WG.Config.AllowedRemovalConverseSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def removeAllMark (ids : List PeerId) : M Unit := do
  for pid in ids do
    _ ← branch .peerRemoveAllIter1 true
    peerMakeDead pid
  _ ← branch .peerRemoveAllIter1 false

def removeAllCleanup (ids : List PeerId) : M Unit := do
  for pid in ids do
    _ ← branch .peerRemoveAllIter2 true
    peerRemoveAfterDead pid
  _ ← branch .peerRemoveAllIter2 false

theorem removeAllMark_cons (pid : PeerId) (rest : List PeerId) :
    removeAllMark (pid :: rest) = (do
      _ ← branch .peerRemoveAllIter1 true
      peerMakeDead pid
      removeAllMark rest) := by
  simp [removeAllMark, List.forIn_cons, List.forIn_nil, bind_assoc]

theorem peerRemoveAll_phases : peerRemoveAll = (do
    free
    let selected := (← getDev).peerList
    removeAllMark selected
    removeAllCleanup selected) := by
  simp only [peerRemoveAll, removeAllMark, removeAllCleanup, bind_assoc, pure_bind]

theorem removeAllMark_effect (ids : List PeerId) (d : Device)
    (pairs : NodePairs d) (listed : ListedResidents d ids) :
    Ensures (removeAllMark ids) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ DeadPassEffect d ids final) := by
  induction ids generalizing d with
  | nil =>
    rw [ensures_iff]
    simp only [removeAllMark, List.forIn_nil, pure_bind]
    mvcgen [branch]
    all_goals exact ⟨d, by assumption, .nil d⟩
  | cons pid rest ih =>
    obtain ⟨p, resident⟩ := listed pid (by simp)
    have head : Ensures (branch .peerRemoveAllIter1 true)
        (fun w => w.k.wg = some d) (fun _ w => w.k.wg = some d) := by
      rw [ensures_iff]
      mvcgen [branch]
    rw [removeAllMark_cons]
    refine ensures_bind _ _ head (fun _ => ?_)
    refine ensures_bind _ _ (peerMakeDead_effect_pairs pid d p resident pairs) ?_
    intro u w result out pre run
    obtain ⟨removed, steps, device⟩ := pre
    have nextListed : ListedResidents (deadPeerDevice removed pid p) rest := by
      intro other member
      obtain ⟨q, found⟩ := listed other (List.mem_cons_of_mem pid member)
      obtain ⟨next, nextResident, deadness⟩ := deadStep_residents d removed pid other p q steps resident found
      exact ⟨next, nextResident⟩
    obtain ⟨final, actual, tail⟩ := ih (deadPeerDevice removed pid p)
      (deadStep_nodePairs d removed pid p steps pairs) nextListed w result out device run
    exact ⟨final, actual, .cons d pid rest p removed final resident steps tail⟩

end Leanux.Proofs.WG.Config
