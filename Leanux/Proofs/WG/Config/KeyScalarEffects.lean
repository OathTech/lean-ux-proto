import Leanux.Proofs.WG.Config.GetterScalarEffects
import Leanux.Proofs.WG.Config.ExpiryEffects

/-! Scalar effects of key invalidation and expiry, independent of operational traversal. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise
theorem invalidate_values (d : Device) (key : Option KeypairId) :
    values (some (invalidateDevice d key))=values (some d) := by
  cases key with
  | none=>rfl
  | some id=>
    simp only [invalidateDevice]
    split <;> rfl

theorem expired_values (pid : PeerId) (d : Device) (p : Peer) (now : Int64)
    (resident : d.peers[pid]?=some p) :
    values (some (expiredDevice d pid p now))=values (some d) := by
  rw [expiredDevice,invalidate_values,invalidate_values]
  funext target
  by_cases eq : target=pid
  · subst target
    simp [values,expiryHeadDevice,withPeer,cell,zeroedHandshake,resident]
  · simp [values,expiryHeadDevice,withPeer,Std.TreeMap.getElem?_insert,Ne.symm eq]

end Leanux.Proofs.WG.Config.GetterScalar
