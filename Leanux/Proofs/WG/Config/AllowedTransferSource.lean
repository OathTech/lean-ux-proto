import Leanux.Proofs.WG.Config.AllowedTransferOperations

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem addPlaced_exact_returns (root : Slot) (bits addr cidr : Nat) (d : Device)
    (id : NodeId) (n : AipNode) (target : PeerId) (p : Peer)
    (node : d.nodes[id]? = some n) (resident : d.peers[target]? = some p) :
    Returns (addPlacedSource root bits addr cidr target (some id) true)
      (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some (transferRootDevice d id n target p)) := by
  let owned := { d with nodes := d.nodes.insert id { n with peer := some target } }
  let unlisted := deleteListedNodes id owned owned.peers.toList
  have hl := (returns_iff _ _ _).mp (listDel_returns id owned)
  have hg : ⦃fun w => ⌜w.k.wg = some unlisted⌝⦄ getPeer target
      ⦃⇓ q w => ⌜q = eraseListedPeer id p ∧ w.k.wg = some unlisted⌝⦄ := by
    mvcgen [getPeer, getDev, getK, invariant]
    all_goals simp_all [unlisted, deleteListedNodes_lookup, owned, resident]
  rw [returns_iff]
  simp [addPlacedSource, branch, bind_assoc]
  mvcgen [getNode, getDev, getK, setNode, modifyDev, modifyK, invariant, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [owned]
  all_goals subst_vars
  all_goals mvcgen [listAddTail, hg, setPeer, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [transferRootDevice, transferredPeer, eraseListedPeer, owned]
  all_goals subst_vars
  all_goals try simp_all

theorem addRoot_exact_returns (v4 : Bool) (d : Device) (id : NodeId) (addr cidr : Nat)
    (owner : Option PeerId) (parent : Slot) (target : PeerId) (p : Peer)
    (width : cidr ≤ allowedBits v4)
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) owner with parent })
    (resident : d.peers[target]? = some p) :
    Returns (addRootSource (allowedRoot v4) (allowedBits v4) addr cidr target (some id))
      (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some
        (transferRootDevice d id { newNode addr cidr (allowedBits v4) owner with parent } target p)) := by
  have hn := (returns_iff _ _ _).mp (placement_first v4 d id addr cidr owner parent width node)
  have ht := (returns_iff _ _ _).mp
    (addPlaced_exact_returns (allowedRoot v4) (allowedBits v4) addr cidr d id _ target p node resident)
  rw [returns_iff]
  simp [addRootSource, branch, bind_assoc]
  mvcgen [hn]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals subst_vars
  all_goals first | omega | exact ht _ (by assumption)

theorem add_root_transfer (v4 : Bool) (d : Device) (id : NodeId) (addr cidr : Nat)
    (owner : Option PeerId) (parent : Slot) (target : PeerId) (p : Peer)
    (width : cidr ≤ allowedBits v4) (root : allowedRootValue v4 d = some id)
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) owner with parent })
    (resident : d.peers[target]? = some p) :
    Returns (add (allowedRoot v4) (allowedBits v4) addr cidr (some target))
      (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some
        (transferRootDevice d id { newNode addr cidr (allowedBits v4) owner with parent } target p)) := by
  have ht := (returns_iff _ _ _).mp
    (addRoot_exact_returns v4 d id addr cidr owner parent target p width node resident)
  rw [add_transfer_source, returns_iff]
  cases v4
  all_goals simp only [allowedRoot, allowedBits, Bool.false_eq_true, ite_false, ite_true] at *
  all_goals mvcgen [slotGet, getDev, getK, branch, branchCmp, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [allowedRootValue]
  all_goals subst_vars
  all_goals first | omega | exact ht _ (by assumption)

end Leanux.Proofs.WG.Config
