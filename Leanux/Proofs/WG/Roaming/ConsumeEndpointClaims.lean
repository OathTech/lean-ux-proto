import Leanux.Proofs.WG.Roaming.ConsumeEndpointSource
import Leanux.Proofs.WG.Roaming.View

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- Original data admission cannot alter any remote endpoint on normal return.
This is before decryption/NAPI: every entry, byte string, source and DS value is
allowed, and no authentication, reference or queue-readiness premise is added. -/
theorem consumeData_preserves_endpoints (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (consumeData msg src ds) (fun s => s = entry)
      (fun _ final => responseEndpointMap final.wg.device = responseEndpointMap entry.wg.device ∧
        ∀ pid, remoteAt final pid = remoteAt entry pid) := by
  intro g ambient result final after pre run
  subst entry
  have same := consumeData_endpoints msg src ds g.dev g ambient result final after rfl run
  refine ⟨same,?_⟩
  intro pid
  have point := congrFun same pid
  have remote := congrArg (fun endpoint : Option (Option Endpoint) => endpoint.join.map destination) point
  have joinMap (p : Option Peer) : (p.map Peer.endpoint).join = p.bind Peer.endpoint := by
    cases p <;> rfl
  simpa only [responseEndpointMap,joinMap,remoteAt,Campaign2.Snapshot.peerAt,
    Campaign2.snapshot,Campaign2.core] using remote

end Leanux.Proofs.WG.Roaming
