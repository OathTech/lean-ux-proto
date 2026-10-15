import Leanux.Proofs.WG.Lifetimes.AllocationAmbient
import Leanux.Proofs.WG.Peers.Allocation

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Successful-state geometry of the original peer creation call. The existing
peer-snapshot theorem supplies its identity transition; these frames add the
other lifetime families and allocation cursors without changing observers. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def peerInitView (w : World) := (otherResidents w, allocationMetadata w)

theorem peerInit_sameKernel (ha : SameKernel a) : SameView peerInitView a := by
  intro w x v hr
  unfold peerInitView otherResidents keypairResidents packetResidents allocationMetadata
  rw [ha w x v hr]

theorem dstCacheReset_peerInitView (pid : PeerId) : SameView peerInitView (dstCacheReset pid) := by
  apply SameView.of_wp
  intro s
  have time_spec := (peerInit_sameKernel (hiddenJiffies_sameKernel .dstCacheResetTs)).wp (fun t => t = s)
  mvcgen [dstCacheReset, time_spec, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals try unfold peerInitView at *
  all_goals try unfold otherResidents at *
  all_goals try unfold keypairResidents at *
  all_goals try unfold packetResidents at *
  all_goals try unfold allocationMetadata at *
  all_goals simp_all [deviceAllocationMetadata]
  all_goals subst_vars
  all_goals simp_all [deviceAllocationMetadata]

theorem resetLastSentHandshake_peerInitView (pid : PeerId) :
    SameView peerInitView (resetLastSentHandshake pid) := by
  apply SameView.of_wp
  intro s
  have time_spec := (peerInit_sameKernel (hiddenClock64_sameKernel .resetLastSent)).wp (fun t => t = s)
  mvcgen [resetLastSentHandshake, time_spec, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals try unfold peerInitView at *
  all_goals try unfold otherResidents at *
  all_goals try unfold keypairResidents at *
  all_goals try unfold packetResidents at *
  all_goals try unfold allocationMetadata at *
  all_goals simp_all [deviceAllocationMetadata]
  all_goals subst_vars
  all_goals simp_all [deviceAllocationMetadata]

theorem precomputeStaticStatic_peerInitView (pid : PeerId) :
    SameView peerInitView (precomputeStaticStatic pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [precomputeStaticStatic, requireNotPending, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals try unfold peerInitView at *
  all_goals try unfold otherResidents at *
  all_goals try unfold keypairResidents at *
  all_goals try unfold packetResidents at *
  all_goals try unfold allocationMetadata at *
  all_goals simp_all [deviceAllocationMetadata]
  all_goals subst_vars
  all_goals simp_all

theorem handshakeInit_peerInitView (pid : PeerId) (psk : Option Key) :
    SameView peerInitView (handshakeInit pid psk) := by
  apply SameView.of_wp
  intro s
  have precompute_spec := (precomputeStaticStatic_peerInitView pid).wp (fun t => t = s)
  mvcgen [handshakeInit, IndexOwner.setPeerWord, precompute_spec, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals try unfold peerInitView at *
  all_goals try unfold otherResidents at *
  all_goals try unfold keypairResidents at *
  all_goals try unfold packetResidents at *
  all_goals try unfold allocationMetadata at *
  all_goals simp_all [deviceAllocationMetadata]
  all_goals subst_vars
  all_goals simp_all [deviceAllocationMetadata]

def peerCreateMetadata (m : AllocationMetadata) : Except Int PeerId → AllocationMetadata
  | .error _ => m
  | .ok pid => {m with device := m.device.map fun d => {d with nextPeer := pid + 1}}

def PeerCreationGeometry (w : World) (result : Except Int PeerId) (v : World) : Prop :=
  otherResidents v = otherResidents w ∧
  allocationMetadata v = peerCreateMetadata (allocationMetadata w) result ∧
  match result with
  | .error _ => True
  | .ok pid => w.k.wg.map (·.nextPeer) = some pid

theorem peerCreate_geometry_wp (start : World) (key : Key) (psk : Option Key) :
    ⦃fun w => ⌜w.k = start.k⌝⦄ peerCreate key psk
    ⦃⇓? result w => ⌜PeerCreationGeometry start result w⌝⦄ := by
  let after := fun pid (s : ((KeypairId → Option Nat) × (Packets.Slot → Option PacketStamp)) × AllocationMetadata) =>
    s.1 = otherResidents start ∧
    s.2 = peerCreateMetadata (allocationMetadata start) (.ok pid) ∧
    start.k.wg.map (·.nextPeer) = some pid
  have alloc_spec := sameKernel_wp _ (hiddenAlloc_sameKernel .kmemCacheZallocPeer)
    (fun k => k = start.k)
  have reset_spec := fun pid => (dstCacheReset_peerInitView pid).wp (after pid)
  have handshake_spec := fun pid => (handshakeInit_peerInitView pid psk).wp (after pid)
  have time_spec := fun pid => (resetLastSentHandshake_peerInitView pid).wp (after pid)
  mvcgen [peerCreate, alloc_spec, reset_spec, handshake_spec, time_spec,
    getDev, getK, setPeer, modifyDev, modifyK, branch, branchCmp, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals try dsimp only [after] at *
  all_goals try unfold PeerCreationGeometry at *
  all_goals try unfold peerInitView at *
  all_goals try unfold otherResidents at *
  all_goals try unfold keypairResidents at *
  all_goals try unfold packetResidents at *
  all_goals try unfold allocationMetadata at *
  all_goals try unfold peerCreateMetadata at *
  all_goals simp_all [deviceAllocationMetadata, Option.bind_map, Option.map_map, Function.comp_def]

theorem peerCreate_geometry (key : Key) (psk : Option Key) (w v : World)
    (result : Except Int PeerId) (hr : (peerCreate key psk).run w = .ok (result, v)) :
    PeerCreationGeometry w result v :=
  (hoare_iff_triple _ _ _).mpr (peerCreate_geometry_wp w key psk) w result v rfl hr

end Leanux.Proofs.WG.Lifetimes
