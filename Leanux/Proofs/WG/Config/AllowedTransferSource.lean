import Leanux.Proofs.WG.Config.AllowedTransferOperations
import Leanux.Proofs.WG.Config.AllowedTransferModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem addPlaced_exact_returns (root : Slot) (bits addr cidr : Nat) (d : Device)
    (id : NodeId) (n : AipNode) (target : PeerId) (p : Peer)
    (node : d.nodes[id]? = some n) (resident : d.peers[target]? = some p) :
    Returns (addPlacedSource root bits addr cidr target (some id) true)
      (fun g => g.dev = some d)
      (fun ret g => ret = 0 ∧ g.dev = some (transferRootDevice d id n target p)) := by
  intro g ambient device
  let owned := {d with nodes := d.nodes.insert id {n with peer := some target}}
  let unlisted := deleteListedNodes id owned owned.peers.toList
  let beforeList := {g with dev := some owned}
  let first := {ambient with steps := ambient.steps.push {
    decision := .addExact, outcome := true, netRx := ambient.netRxSection}}
  obtain ⟨done, middle, next, listRun, listEffect⟩ :=
    listDel_returns id owned beforeList first rfl
  cases done
  have targetAt : unlisted.peers[target]? = some (eraseListedPeer id p) := by
    simp [unlisted, deleteListedNodes_lookup, owned, resident]
  let final := {middle with dev := some (transferRootDevice d id n target p)}
  have tail : (((do listAddTail target id; pure (0 : Int)) : WG.M Int).run middle).run next =
      .ok ((0, final), next) := by
    simp [listAddTail, getPeer, getDev, listEffect, targetAt, setPeer, modifyDev,
      final, transferRootDevice, transferredPeer, eraseListedPeer, unlisted, owned]
    rfl
  refine ⟨0, final, next, ?_, rfl, rfl⟩
  have getLift (nid : NodeId) : (monadLift (getNode nid) : WG.M AipNode) =
      liftAip (getNode nid) := rfl
  have setLift (nid : NodeId) (value : AipNode) : (monadLift (setNode nid value) : WG.M Unit) =
      liftAip (setNode nid value) := rfl
  simp only [addPlacedSource, getLift, setLift]
  simp [branch, AmbientM.branch, getNode, setNode, liftAip, getDev, modifyDev,
    device, node, first, beforeList, owned] at listRun ⊢
  rw [listRun]
  exact tail

theorem addRoot_exact_returns (v4 : Bool) (d : Device) (id : NodeId) (addr cidr : Nat)
    (owner : Option PeerId) (parent : Slot) (target : PeerId) (p : Peer)
    (width : cidr ≤ allowedBits v4)
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) owner with parent })
    (resident : d.peers[target]? = some p) :
    Returns (addRootSource (allowedRoot v4) (allowedBits v4) addr cidr target (some id))
      (fun g => g.dev = some d)
      (fun ret g => ret = 0 ∧ g.dev = some
        (transferRootDevice d id { newNode addr cidr (allowedBits v4) owner with parent } target p)) := by
  intro g ambient device
  let first := {ambient with steps := ambient.steps.push {
    decision := .addEmptyTrie, outcome := false, netRx := ambient.netRxSection}}
  obtain ⟨placed, middle, next, placementRun, value, placementDevice⟩ :=
    placement_first v4 d id addr cidr owner parent width node g first device
  subst placed
  obtain ⟨ret, final, after, tailRun, effects⟩ :=
    addPlaced_exact_returns (allowedRoot v4) (allowedBits v4) addr cidr d id
      {newNode addr cidr (allowedBits v4) owner with parent} target p node resident
      middle next placementDevice
  refine ⟨ret, final, after, ?_, effects⟩
  have placementLift : (monadLift (nodePlacement (some id) addr cidr (allowedBits v4)) :
      WG.M (Option NodeId × Bool)) =
      liftAip (nodePlacement (some id) addr cidr (allowedBits v4)) := rfl
  simp only [addRootSource, placementLift]
  simp [branch, AmbientM.branch]
  change (((liftAip (nodePlacement (some id) addr cidr (allowedBits v4))).run g).run first >>=
    fun ((r, g'), a') =>
      ((addPlacedSource (allowedRoot v4) (allowedBits v4) addr cidr target r.1 r.2).run g').run a') = _
  rw [placementRun]
  exact tailRun

theorem add_root_transfer (v4 : Bool) (d : Device) (id : NodeId) (addr cidr : Nat)
    (owner : Option PeerId) (parent : Slot) (target : PeerId) (p : Peer)
    (width : cidr ≤ allowedBits v4) (root : allowedRootValue v4 d = some id)
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) owner with parent })
    (resident : d.peers[target]? = some p) :
    Returns (add (allowedRoot v4) (allowedBits v4) addr cidr (some target))
      (fun g => g.dev = some d)
      (fun ret g => ret = 0 ∧ g.dev = some
        (transferRootDevice d id { newNode addr cidr (allowedBits v4) owner with parent } target p)) := by
  intro g ambient device
  let marked := {ambient with steps := ambient.steps.push {
    decision := .addCidrTooLong, outcome := false,
    operands := some (Int.ofNat cidr, Int.ofNat (allowedBits v4)), netRx := ambient.netRxSection}}
  let before := {marked with steps := marked.steps.push {
    decision := .addNoPeer, outcome := false, netRx := marked.netRxSection}}
  let middle := {g with dev := some d}
  obtain ⟨ret, final, after, tailRun, effects⟩ :=
    addRoot_exact_returns v4 d id addr cidr owner parent target p width node resident
      middle before rfl
  refine ⟨ret, final, after, ?_, effects⟩
  rw [add_transfer_source]
  have slotLift (slot : Slot) : (monadLift (slotGet slot) : WG.M (Option NodeId)) =
      liftAip (slotGet slot) := rfl
  simp only [slotLift]
  have noLong : ¬ allowedBits v4 < cidr := Nat.not_lt.mpr width
  simp [branchCmp, AmbientM.branchCmp, branch, AmbientM.branch, noLong]
  cases v4
  all_goals
    simp [slotGet, liftAip, getDev, modifyDev, device, allowedRoot, allowedRootValue] at root ⊢
    simpa [root, middle, before, marked, allowedRoot, allowedBits] using tailRun

end Leanux.Proofs.WG.Config
