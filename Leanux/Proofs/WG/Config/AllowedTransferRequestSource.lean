import Leanux.Proofs.WG.Config.AllowedTransferSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem setAllowedip_root_transfer (v4 : Bool) (d : Device) (id : NodeId) (addr cidr : Nat)
    (owner : Option PeerId) (parent : Slot) (target : PeerId) (p : Peer)
    (width : cidr ≤ allowedBits v4) (root : allowedRootValue v4 d = some id)
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) owner with parent })
    (resident : d.peers[target]? = some p) :
    Returns (setAllowedip target (allowedAttrs v4 addr cidr))
      (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some
        (transferRequestDevice d id { newNode addr cidr (allowedBits v4) owner with parent } target p)) := by
  have ha := (returns_iff _ _ _).mp
    (add_root_transfer v4 (insertSequenceDevice d) id addr cidr owner parent target p width root node resident)
  rw [returns_iff]
  cases v4
  all_goals simp [allowedAttrs, allowedBits, allowedRoot, insertSequenceDevice] at ha width
  all_goals mvcgen [setAllowedip, Leanux.WG.insert, getDev, getK, modifyDev, modifyK,
    branch, WG.andM, WG.orM, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [allowedAttrs, AF_INET, AF_INET6, transferRequestDevice, insertSequenceDevice]
  all_goals subst_vars
  all_goals mvcgen [ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

end Leanux.Proofs.WG.Config
