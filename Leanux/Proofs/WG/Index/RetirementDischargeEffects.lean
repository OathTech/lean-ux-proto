import Leanux.Proofs.WG.Index.RetirementRetentionEffects
import Leanux.Proofs.WG.Index.HashSlotClearClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits

/-- Empty slots exclude every hashed key naming the paid owner, so its
retirement occurrence can be discharged without assuming list distinctness. -/
theorem cleared_retirement_discharge (paid : Owner) (retired : Reservations) (d : Device)
    (covered : HashSlotCoverage d) (reserved : DeadHashedReserved (paid :: retired) d)
    (empty : ∀ p, d.peers[paid.slot]? = some p → clearKeys p = [none,none,none]) :
    DeadHashedReserved retired d := by
  intro entry member kid key pid p owner keyFound keyPeer peerFound dead
  have saved := reserved entry member kid key pid p owner keyFound keyPeer peerFound dead
  rcases List.mem_cons.mp saved with same | kept
  · have slotEqual : pid = paid.slot := congrArg Owner.slot same
    obtain ⟨target,q,k,found,kfound,kpeer,slot⟩ := covered entry member kid owner
    have keyEq : k = key := Option.some.inj (kfound.symm.trans keyFound)
    subst k
    have targetEq : target = pid := Option.some.inj (kpeer.symm.trans keyPeer)
    subst target
    have peerEq : q = p := Option.some.inj (found.symm.trans peerFound)
    subst q
    have emptySlots := empty p (by simpa only [slotEqual] using peerFound)
    simp only [emptySlots,List.mem_cons,List.not_mem_nil,Option.some_ne_none,
      or_self] at slot
  · exact kept

end Leanux.Proofs.WG.Index
