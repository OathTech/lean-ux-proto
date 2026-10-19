import Leanux.Proofs.WG.Config.ConfiguredRemovalSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise AllowedIps
open Leanux.Proofs.Framing Lifetimes Queues.RxCredits Std.Do

/-- The original normal make-dead call derives the target resident and removes
its exact represented route set, starting only from represented configured owners. -/
theorem peerMakeDead_configured_owners (d : Device) (t4 t6 : Tree) (pid : PeerId)
    (routing : RoutingInvariant d t4 t6) (owners : ConfiguredOwners d t4 t6) :
    Campaign2.Ensures (peerMakeDead pid) (fun s=>s.wg.device=some d)
      (fun _ s=>∃ out p, s.wg.device=some out ∧ d.peers[pid]?=some p ∧
        out.peerList=d.peerList.filter (· != pid) ∧
        RoutingInvariant out (t4.eraseIds p.allowedipsList) (t6.eraseIds p.allowedipsList) ∧
        ConfiguredOwners out (t4.eraseIds p.allowedipsList) (t6.eraseIds p.allowedipsList)) :=
  peerMakeDead_configured_run d t4 t6 pid routing owners

/-- The actual cleanup tail preserves configured ownership even when its
reference payments delete peer objects. Resident route owners are a separate claim. -/
theorem peerRemoveAfterDead_configured_owners (d : Device) (t4 t6 : Tree)
    (pid : PeerId) (routing : RoutingInvariant d t4 t6)
    (owners : ConfiguredOwners d t4 t6) :
    Campaign2.Ensures (peerRemoveAfterDead pid) (fun s=>s.wg.device=some d)
      (fun _ s=>∃ out,s.wg.device=some out ∧ out.peerList=d.peerList ∧
        RoutingInvariant out t4 t6 ∧ ConfiguredOwners out t4 t6) :=
  peerRemoveAfterDead_configured_run d t4 t6 pid routing owners

/-- Complete original null/selected removal, including actual cleanup and
its possible Stops. Every normal return retains represented configured ownership. -/
theorem peerRemove_configured_owners (d : Device) (t4 t6 : Tree)
    (peer : Option PeerId) (routing : RoutingInvariant d t4 t6)
    (owners : ConfiguredOwners d t4 t6) :
    Campaign2.Ensures (peerRemove peer) (fun s=>s.wg.device=some d)
      (fun _ s=>∃ out u4 u6,s.wg.device=some out ∧
        RoutingInvariant out u4 u6 ∧ ConfiguredOwners out u4 u6) :=
  peerRemove_configured_run d t4 t6 peer routing owners

end Leanux.Proofs.WG.Config
