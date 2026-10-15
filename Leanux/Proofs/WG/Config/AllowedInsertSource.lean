import Leanux.Proofs.WG.Config.AllowedInsertModel
import Leanux.Proofs.WG.Config.Returns
import Leanux.Proofs.WG.Config.AllowedInsertFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem allocRootNode_effect (n : AipNode) (d : Device) :
    Ensures (allocNode .allocNode190 n) (fun w => w.k.wg = some d)
      (fun result w => match result with
        | none => w.k.wg = some d
        | some id => id = d.nextNode ∧ w.k.wg = some
            { d with nextNode := id + 1, nodes := d.nodes.insert id n }) := by
  have ha := hiddenAlloc_sameKernel_node_spec_variant (fun k => k.wg = some d)
  rw [ensures_iff]
  mvcgen [allocNode, getDev, getK, modifyDev, modifyK, invariant, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem add_empty_root_effect (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (addr cidr : Nat) (resident : d.peers[pid]? = some p)
    (root : allowedRootValue v4 d = none) (width : cidr ≤ allowedBits v4) :
    Ensures (add (allowedRoot v4) (allowedBits v4) addr cidr (some pid))
      (fun w => w.k.wg = some d)
      (fun ret w => (ret = -ENOMEM ∧ w.k.wg = some d) ∨
        (ret = 0 ∧ w.k.wg = some (emptyRootInserted v4 d pid p addr cidr))) := by
  have ha := (ensures_iff _ _ _).mp
    (allocRootNode_effect (newNode addr cidr (allowedBits v4) (some pid)) d)
  have hn (trie : Option NodeId) (key cidr bits : Nat) :
      ⦃fun _ => ⌜True⌝⦄ nodePlacement trie key cidr bits ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w result final pre run
    trivial
  rw [ensures_iff]
  cases v4
  all_goals simp only [allowedRoot, allowedBits, Bool.false_eq_true, ite_false, ite_true] at *
  all_goals mvcgen [add, slotGet, slotSet, listAddTail, connectNode, getDev, getPeer,
    getNode, getK, setPeer, setNode, modifyDev, modifyK, branch, branchCmp, invariant, ha, hn]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [allowedRootValue, emptyRootInserted, allowedBits, allowedRoot, newNode]
  all_goals subst_vars
  all_goals try simp_all [allowedAttrs, allowedRootValue, emptyRootInserted, allowedBits, allowedRoot, newNode]
  all_goals try omega
  all_goals grind only

theorem setAllowedip_empty_root_effect (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (addr cidr : Nat) (resident : d.peers[pid]? = some p)
    (root : allowedRootValue v4 d = none) (width : cidr ≤ allowedBits v4) :
    Ensures (setAllowedip pid (allowedAttrs v4 addr cidr)) (fun w => w.k.wg = some d)
      (fun ret w => ∃ final, w.k.wg = some final ∧ EmptyRootInsertEffect v4 d pid p addr cidr ret final) := by
  have ha := (ensures_iff _ _ _).mp
    (add_empty_root_effect v4 (insertSequenceDevice d) pid p addr cidr resident root width)
  rw [ensures_iff]
  cases v4
  all_goals simp [allowedAttrs, allowedBits, allowedRoot, insertSequenceDevice] at ha width
  all_goals mvcgen [setAllowedip, Leanux.WG.insert, getDev, getK, modifyDev, modifyK,
    branch, WG.andM, WG.orM, invariant, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [allowedAttrs, AF_INET, AF_INET6, EmptyRootInsertEffect, insertSequenceDevice]
  all_goals subst_vars
  all_goals try simp_all [allowedAttrs, allowedRootValue, emptyRootInserted, allowedBits, allowedRoot, newNode]
  all_goals try omega

  all_goals mvcgen [ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [EmptyRootInsertEffect]
  all_goals grind only

end Leanux.Proofs.WG.Config
