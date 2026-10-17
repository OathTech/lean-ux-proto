import Leanux.Proofs.WG.Config.AllowedTransferSource
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do
theorem setAllowedip_root_transfer (v4 : Bool) (d : Device) (id : NodeId) (addr cidr : Nat)
    (owner : Option PeerId) (parent : Slot) (target : PeerId) (p : Peer)
    (width : cidr ≤ allowedBits v4) (root : allowedRootValue v4 d = some id)
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) owner with parent })
    (resident : d.peers[target]? = some p) :
    Returns (setAllowedip target (allowedAttrs v4 addr cidr))
      (fun g => g.dev = some d)
      (fun ret g => ret = 0 ∧ g.dev = some
        (transferRequestDevice d id { newNode addr cidr (allowedBits v4) owner with parent } target p)) := by
  have ha := add_root_transfer v4 (insertSequenceDevice d) id addr cidr owner parent target p
    width root node resident
  intro g ambient device
  cases v4
  all_goals
    simp only [allowedBits, allowedRoot, Bool.false_eq_true, ite_false, ite_true] at ha width
    simp only [Returns, exists_and_right] at ha
    simp [setAllowedip, allowedAttrs, AF_INET, AF_INET6, branch, AmbientM.branch,
      WG.andM, WG.orM, Leanux.WG.insert, modifyDev, device, width, transferRequestDevice]
    exact ha {g with dev := some (insertSequenceDevice d)} _ rfl
end Leanux.Proofs.WG.Config
