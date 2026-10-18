import Leanux.Proofs.WG.Index.OwnerCoherenceExpiryClaims
import Leanux.Proofs.WG.Index.RetirementModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits

/-- Sending-key invalidation preserves the structural index fields exactly. -/
theorem invalidateDevice_indexFields (d : Device) (key : Option KeypairId) :
    let final := Config.invalidateDevice d key
    (final.indexTable,final.peers,final.ifindex,final.nextKeypairId) =
      (d.indexTable,d.peers,d.ifindex,d.nextKeypairId) := by
  cases key with
  | none => rfl
  | some kid => cases found : d.keypairs[kid]? <;> simp [Config.invalidateDevice,found]
end Leanux.Proofs.WG.Index
