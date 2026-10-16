import Leanux.Proofs.WG.Peers.Primitives

set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Peer identity framing for original helpers. The live getter/setter pair
retains the stamp returned by the getter as well as an arbitrary predicate.
This supplies provenance for updates of a cached peer record. -/
namespace Leanux.Proofs.WG.Peers
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.WG.Lifetimes

def SamePeerSnapshot (a : M α) : Prop :=
  ProjectedAction snapshot (fun s t => t = s) a

def snapshotOfWGKernelView (v : WGKernelView) : Store PeerId :=
  ⟨v.peerCounter, fun i => (v.wg.bind fun d => d.peers[i]?).map (·.internalId)⟩

theorem samePeerSnapshot_of_sameWGKernel (h : SameWGKernel a) : SamePeerSnapshot a :=
  h.of_factor snapshotOfWGKernelView snapshot (fun _ => rfl)

theorem SamePeerSnapshot.wp (h : SamePeerSnapshot a) (P : Store PeerId → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ a ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  ProjectedAction.wp h P (fun _ _ he hp => he ▸ hp)

theorem samePeerSnapshot_of_wp (a : M α)
    (h : ∀ s, ⦃fun w => ⌜snapshot w = s⌝⦄ a
      ⦃⇓? _ w => ⌜snapshot w = s⌝⦄) : SamePeerSnapshot a :=
  ProjectedAction.of_wp snapshot (fun s t => t = s) a h

theorem samePeerSnapshot_of_sameKernel (h : SameKernel a) : SamePeerSnapshot a := by
  intro w x w' hr
  simp only [snapshot, h w x w' hr]

theorem getPeer_live_spec (P : Store PeerId → Prop) (i : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ getPeer i
    ⦃⇓? p w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some p.internalId⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w p w' hp hr
  obtain ⟨rfl, hi⟩ := getPeer_current i w w' p hr
  exact ⟨hp, hi⟩

theorem setPeer_live_spec (P : Store PeerId → Prop) (i : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some p.internalId⌝⦄ setPeer i p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hp hr
  cases x
  rw [setPeer_same i p w w' hp.2 hr]
  exact hp.1

theorem modifyDev_peer_spec (P : Store PeerId → Prop) (f : Device → Device)
    (hf : ∀ d, (f d).peers = d.peers) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hp hr
  cases hr
  simpa [snapshot, modifyDev, modifyK, Option.bind_map, Function.comp_def, hf] using hp

theorem hiddenU64_sameKernel (site : HiddenSite) : SameKernel (hiddenU64 site) := by
  unfold hiddenU64
  exact sameKernel_bind (hidden_sameKernel site) (fun _ => sameKernel_pure _)

theorem hiddenU64_peer_spec (P : Store PeerId → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ hiddenU64 site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (samePeerSnapshot_of_sameKernel (hiddenU64_sameKernel site)).wp P

theorem hiddenClock_peer_spec (P : Store PeerId → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ hiddenClock site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (samePeerSnapshot_of_sameKernel (Keypairs.hiddenClock_sameKernel site)).wp P

theorem hiddenJiffies_peer_spec (P : Store PeerId → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ hiddenJiffies site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (samePeerSnapshot_of_sameKernel (Framing.hiddenJiffies_sameKernel site)).wp P

theorem hiddenClock64_peer_spec (P : Store PeerId → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ hiddenClock64 site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (samePeerSnapshot_of_sameKernel (Framing.hiddenClock64_sameKernel site)).wp P

theorem hiddenAlloc_peer_spec (P : Store PeerId → Prop) (site : AllocSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ hiddenAlloc site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (samePeerSnapshot_of_sameKernel (Keypairs.hiddenAlloc_sameKernel site)).wp P

theorem requireNotPending_samePeerSnapshot (pid : PeerId) (what : String) :
    SamePeerSnapshot (requireNotPending pid what) := by
  apply samePeerSnapshot_of_wp
  intro s
  have get_spec := getPeer_live_spec (fun t => t = s)
  mvcgen [requireNotPending, get_spec, unsupported]
  all_goals simp_all

theorem requireNotPending_peer_spec (P : Store PeerId → Prop) (pid : PeerId) (what : String) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ requireNotPending pid what
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (requireNotPending_samePeerSnapshot pid what).wp P

theorem peerGetMaybeZero_samePeerSnapshot (peer : Option PeerId) :
    SamePeerSnapshot (peerGetMaybeZero peer) := by
  apply samePeerSnapshot_of_wp
  intro s
  have get_spec := getPeer_live_spec (fun t => t = s)
  have set_spec := setPeer_live_spec (fun t => t = s)
  have pending_spec := requireNotPending_peer_spec (fun t => t = s)
  mvcgen [peerGetMaybeZero, pending_spec, get_spec, set_spec,
    refcountIncNotZero, branch, branchCmp, unsupported, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [snapshot]

theorem dstCacheReset_samePeerSnapshot (pid : PeerId) : SamePeerSnapshot (dstCacheReset pid) := by
  apply samePeerSnapshot_of_wp
  intro s
  have get_spec := getPeer_live_spec (fun t => t = s)
  have set_spec := setPeer_live_spec (fun t => t = s)
  have time_spec := hiddenJiffies_peer_spec (fun t => t = s)
  mvcgen [dstCacheReset, get_spec, set_spec, time_spec]
  all_goals simp_all

theorem resetLastSentHandshake_samePeerSnapshot (pid : PeerId) :
    SamePeerSnapshot (resetLastSentHandshake pid) := by
  apply samePeerSnapshot_of_wp
  intro s
  have get_spec := getPeer_live_spec (fun t => t = s)
  have set_spec := setPeer_live_spec (fun t => t = s)
  have time_spec := hiddenClock64_peer_spec (fun t => t = s)
  mvcgen [resetLastSentHandshake, get_spec, set_spec, time_spec]
  all_goals simp_all

theorem precomputeStaticStatic_samePeerSnapshot (pid : PeerId) :
    SamePeerSnapshot (precomputeStaticStatic pid) := by
  apply samePeerSnapshot_of_wp
  intro s
  have get_spec := getPeer_live_spec (fun t => t = s)
  have set_spec := setPeer_live_spec (fun t => t = s)
  have pending_spec := requireNotPending_peer_spec (fun t => t = s)
  mvcgen [precomputeStaticStatic, pending_spec, get_spec, set_spec,
    getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [snapshot]

theorem handshakeInit_samePeerSnapshot (pid : PeerId) (psk : Option Key) :
    SamePeerSnapshot (handshakeInit pid psk) := by
  apply samePeerSnapshot_of_wp
  intro s
  have get_spec := getPeer_live_spec (fun t => t = s)
  have set_spec := setPeer_live_spec (fun t => t = s)
  have precompute_spec := (precomputeStaticStatic_samePeerSnapshot pid).wp (fun t => t = s)
  mvcgen [handshakeInit, IndexOwner.setPeerWord, get_spec, set_spec, precompute_spec, branch]
  all_goals simp_all [snapshot]

end Leanux.Proofs.WG.Peers
