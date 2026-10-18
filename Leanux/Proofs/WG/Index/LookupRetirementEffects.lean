import Leanux.Proofs.WG.Index.RetirementRetentionEffects
import Leanux.Proofs.WG.Index.OwnerCoherenceFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem writeSame_deadHashedReserved (retired : Reservations) (d : Device)
    (owner : IndexOwner) (word : Option PeerId) (same : ownerWord d owner=some word)
    (safe : DeadHashedReserved retired d) :
    DeadHashedReserved retired (writeOwnerWord d owner word) := by
  apply deadHashedReserved_transport retired d _ _ _ _ _ safe
  · cases owner <;> simp only [writeOwnerWord] <;> split <;> rfl
  · intro entry member
    have table : (writeOwnerWord d owner word).indexTable=d.indexTable := by
      cases owner <;> simp only [writeOwnerWord] <;> split <;> rfl
    simpa only [table] using member
  · intro entry member kid own
    simp only [own,ownerWord,writeOwnerWord_same_keypairs d owner word same]
  · intro pid p found
    exact ⟨p,(writeOwnerWord_same_peers d owner word same pid).symm.trans found,rfl,rfl⟩


end Leanux.Proofs.WG.Index
