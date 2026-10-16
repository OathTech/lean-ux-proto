import Leanux.Proofs.WG.Lifetimes.AllocationAmbient
import Leanux.Proofs.WG.Peers.Allocation

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Successful-state geometry of the original peer creation call. The existing
peer-snapshot theorem supplies its identity transition; these frames add the
other lifetime families and allocation cursors without changing observers. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def peerInitView (w : WGWorld) := (otherResidents w, allocationMetadata w)

theorem peerInit_sameWGStore
    {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => wgStoreView (project s)) a) :
    SameView (fun s => peerInitView (project s)) a := by
  have residents := (identity_sameWGStore ha).factor (fun s : IdentityView => s.2)
  have metadata := ha.of_factor
    (fun s : WGStoreView => (⟨s.keypairCounter, s.netIfindexNext,
      s.dev.map deviceAllocationMetadata⟩ : AllocationMetadata))
    (fun s => allocationMetadata (project s)) (fun _ => rfl)
  exact residents.product metadata

theorem dstCacheReset_peerInitView (pid : PeerId) : SameView peerInitView (dstCacheReset pid) := by
  apply SameView.of_wp
  intro s
  have ambient_spec (α : Type) (a : AmbientM α) :
      ⦃fun w => ⌜peerInitView w = s⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ w => ⌜peerInitView w = s⌝⦄ :=
    hoare_liftAmbient a (fun w => peerInitView w = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, dstCacheReset, getAmbient,
    hiddenJiffies, ambient_spec, getPeer, getDev, setPeer, modifyDev, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals try unfold peerInitView at *
  all_goals try unfold otherResidents at *
  all_goals try unfold keypairResidents at *
  all_goals try unfold packetResidents at *
  all_goals try unfold allocationMetadata at *
  all_goals try dsimp only [deviceAllocationMetadata] at *
  all_goals simp_all [deviceAllocationMetadata, Option.bind_map, Function.comp_def]
  all_goals subst_vars
  all_goals try dsimp only [deviceAllocationMetadata] at *
  all_goals simp_all [deviceAllocationMetadata, Option.bind_map, Function.comp_def]
  all_goals change Option.map deviceAllocationMetadata _ = _
  all_goals simp_all only

theorem resetLastSentHandshake_peerInitView (pid : PeerId) :
    SameView peerInitView (resetLastSentHandshake pid) := by
  apply SameView.of_wp
  intro s
  have ambient_spec (α : Type) (a : AmbientM α) :
      ⦃fun w => ⌜peerInitView w = s⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ w => ⌜peerInitView w = s⌝⦄ :=
    hoare_liftAmbient a (fun w => peerInitView w = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, resetLastSentHandshake,
    hiddenClock64, ambient_spec, getPeer, getDev, setPeer, modifyDev, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals try unfold peerInitView at *
  all_goals try unfold otherResidents at *
  all_goals try unfold keypairResidents at *
  all_goals try unfold packetResidents at *
  all_goals try unfold allocationMetadata at *
  all_goals try dsimp only [deviceAllocationMetadata] at *
  all_goals simp_all [deviceAllocationMetadata, Option.bind_map, Function.comp_def]
  all_goals subst_vars
  all_goals try dsimp only [deviceAllocationMetadata] at *
  all_goals simp_all [deviceAllocationMetadata, Option.bind_map, Function.comp_def]
  all_goals change Option.map deviceAllocationMetadata _ = _
  all_goals simp_all only

theorem precomputeStaticStatic_peerInitView (pid : PeerId) :
    SameView peerInitView (precomputeStaticStatic pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [precomputeStaticStatic, requireNotPending, getPeer, getDev,
    setPeer, modifyDev, branch, invariant, unsupported,
    AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals try unfold peerInitView at *
  all_goals try unfold otherResidents at *
  all_goals try unfold keypairResidents at *
  all_goals try unfold packetResidents at *
  all_goals try unfold allocationMetadata at *
  all_goals try dsimp only [deviceAllocationMetadata] at *
  all_goals simp_all [deviceAllocationMetadata, Option.bind_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem handshakeInit_peerInitView (pid : PeerId) (psk : Option Key) :
    SameView peerInitView (handshakeInit pid psk) := by
  apply SameView.of_wp
  intro s
  have precompute_spec := (precomputeStaticStatic_peerInitView pid).wp (fun t => t = s)
  mvcgen [handshakeInit, IndexOwner.setPeerWord, precompute_spec, getPeer, getDev,
    setPeer, modifyDev, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals try unfold peerInitView at *
  all_goals try unfold otherResidents at *
  all_goals try unfold keypairResidents at *
  all_goals try unfold packetResidents at *
  all_goals try unfold allocationMetadata at *
  all_goals try dsimp only [deviceAllocationMetadata] at *
  all_goals simp_all [deviceAllocationMetadata, Option.bind_map, Function.comp_def]
  all_goals subst_vars
  all_goals try dsimp only [deviceAllocationMetadata] at *
  all_goals simp_all [deviceAllocationMetadata, Option.bind_map, Function.comp_def]

def peerCreateMetadata (m : AllocationMetadata) : Except Int PeerId → AllocationMetadata
  | .error _ => m
  | .ok pid => {m with device := m.device.map fun d => {d with nextPeer := pid + 1}}

def PeerCreationGeometry (w : WGWorld) (result : Except Int PeerId) (v : WGWorld) : Prop :=
  otherResidents v = otherResidents w ∧
  allocationMetadata v = peerCreateMetadata (allocationMetadata w) result ∧
  match result with
  | .error _ => True
  | .ok pid => w.dev.map (·.nextPeer) = some pid

theorem peerCreate_geometry_wp (start : WGWorld) (key : Key) (psk : Option Key) :
    ⦃fun w => ⌜wgStoreView w = wgStoreView start⌝⦄ peerCreate key psk
    ⦃⇓? result w => ⌜PeerCreationGeometry start result w⌝⦄ := by
  let after := fun pid (s : ((KeypairId → Option Nat) × (Packets.Slot → Option PacketStamp)) × AllocationMetadata) =>
    s.1 = otherResidents start ∧
    s.2 = peerCreateMetadata (allocationMetadata start) (.ok pid) ∧
    start.dev.map (·.nextPeer) = some pid
  have alloc_spec :
      ⦃fun w => ⌜wgStoreView w = wgStoreView start⌝⦄
        (hiddenAlloc .kmemCacheZallocPeer : WG.M Bool)
      ⦃⇓? _ w => ⌜wgStoreView w = wgStoreView start⌝⦄ :=
    hoare_liftAmbient (AmbientM.hiddenAlloc .kmemCacheZallocPeer)
      (fun w => wgStoreView w = wgStoreView start)
  have reset_spec := fun pid => (dstCacheReset_peerInitView pid).wp (after pid)
  have handshake_spec := fun pid => (handshakeInit_peerInitView pid psk).wp (after pid)
  have time_spec := fun pid => (resetLastSentHandshake_peerInitView pid).wp (after pid)
  mvcgen [peerCreate, alloc_spec, reset_spec, handshake_spec, time_spec,
    getDev, setPeer, modifyDev, branch, branchCmp, invariant,
    AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals try dsimp only [after] at *
  all_goals try unfold PeerCreationGeometry at *
  all_goals try unfold peerInitView at *
  all_goals try unfold otherResidents at *
  all_goals try unfold keypairResidents at *
  all_goals try unfold packetResidents at *
  all_goals try unfold allocationMetadata at *
  all_goals try unfold peerCreateMetadata at *
  all_goals try dsimp only [deviceAllocationMetadata] at *
  all_goals simp_all [deviceAllocationMetadata, wgStoreView, Option.bind_map, Option.map_map, Function.comp_def]
  all_goals try change Option.map deviceAllocationMetadata _ = _
  all_goals grind only

theorem peerCreate_geometry (key : Key) (psk : Option Key) (w v : WGWorld)
    (result : Except Int PeerId) (ambient ambient' : Ambient)
    (hr : ((peerCreate key psk).run w).run ambient = .ok ((result, v), ambient')) :
    PeerCreationGeometry w result v :=
  (hoare_iff_run_ambient _ _ _).mp (peerCreate_geometry_wp w key psk)
    w ambient result v ambient' rfl hr

end Leanux.Proofs.WG.Lifetimes
