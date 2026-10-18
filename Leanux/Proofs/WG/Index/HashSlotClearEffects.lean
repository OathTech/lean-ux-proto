import Leanux.Proofs.WG.Index.HashSlotClearFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

-- Effects
theorem clearPut_hashSlotCoverage {key : Option KeypairId} {d final : Device}
    (put : ClearPut key d final) (covered : HashSlotCoverage d) :
    HashSlotCoverage final := by
  intro e member kid owner
  have old := (clearPut_retained_owner put e member).1
  obtain ⟨pid,p,k,peer,key,word,slot⟩ := covered e old kid owner
  refine ⟨pid,p,k,?_,?_,word,slot⟩
  · rw [clearPut_peers put]
    exact peer
  · rw [clearPut_hashed_key put e member kid owner]
    exact key

theorem clearStep_hashSlotCoverage (d : Device) (pid : PeerId) (slot : ClearSlot)
    (p : Peer) (final : Device) (resident : d.peers[pid]? = some p)
    (put : ClearPut (slot.read p) (clearWrite d pid slot p) final)
    (covered : HashSlotCoverage d) : HashSlotCoverage final := by
  intro e member kid owner
  have old := clearStep_retained_owner d pid slot p final resident put e member
  obtain ⟨target,peer,k,stored,key,word,inside⟩ := covered e old.1 kid owner
  have keyFinal : final.keypairs[kid]? = some k := by
    rw [clearPut_hashed_key put e member kid owner]
    exact key
  by_cases same : pid = target
  · subst target
    have samePeer : peer = p := Option.some.inj (stored.symm.trans resident)
    subst peer
    refine ⟨pid,slot.clear p,k,old.2.2.2,keyFinal,word,?_⟩
    apply clearSlot_other_membership slot p kid inside
    intro selected
    exact old.2.2.1 kid selected owner
  · refine ⟨target,peer,k,?_,keyFinal,word,inside⟩
    rw [clearPut_peers put]
    simpa [clearWrite,Std.TreeMap.getElem?_insert,same] using stored

theorem clearRun_hashSlotCoverage {pid : PeerId} {d final : Device}
    {slots : List ClearSlot} (steps : ClearRun pid d slots final)
    (covered : HashSlotCoverage d) : HashSlotCoverage final := by
  induction steps with
  | nil => exact covered
  | cons d slot p middle final rest resident put tail ih =>
    exact ih (clearStep_hashSlotCoverage d pid slot p middle resident put covered)

theorem clearRun_hashSlots_detached (pid : PeerId) (d final : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (steps : ClearRun pid d [.next,.previous,.current] final)
    (coherent : HashedOwnersCoherent d) (covered : HashSlotCoverage d) :
    LastOwnerDetached final pid (Config.emptyKeysPeer p) :=
  clearRun_covered_detached pid d final p resident steps
    (hashSlotCoverage_lastOwnerCovered d pid p resident coherent covered)


end Leanux.Proofs.WG.Index
