import Leanux.Proofs.WG.Index.ReceiveOperations
import Leanux.Proofs.WG.Noise.Execution

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- Invalid MAC1 takes the original packet body's early return before any
cookie reply, handshake consumer, endpoint setter, or common receive suffix. -/
theorem receivePacketBody_invalid_mac1 (msg : List UInt8) (src : SkbSource)
    (underLoad : Bool) (d : Device)
    (invalid : blake2s 16 d.mac1Key (msg.take (msg.length - 32)) ≠
      (msg.drop (msg.length - 32)).take 16) :
    Ensures (Index.receivePacketBody msg src underLoad) (fun g => g.dev = some d)
      (fun _ g => g.dev = some d) := by
  intro g ambient result final after device run
  cases underLoad <;>
    simp [Index.receivePacketBody, cookieValidatePacket, getDev, device, invalid,
      WG.andM, WG.orM, branch, AmbientM.branch] at run
  all_goals rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  all_goals exact device

end Leanux.Proofs.WG.Roaming
