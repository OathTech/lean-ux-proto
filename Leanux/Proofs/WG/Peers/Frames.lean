import Leanux.Proofs.WG.Peers.Primitives
import Leanux.Proofs.Framing.WGKernel

set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Peer identity framing for original helpers. The live getter/setter pair
retains the stamp returned by the getter as well as an arbitrary predicate.
This supplies provenance for updates of a cached peer record. -/
namespace Leanux.Proofs.WG.Peers
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.WG.Lifetimes

def SamePeerSnapshot (a : WG.M α) : Prop :=
  ProjectedAction snapshot (fun s t => t = s) a

def snapshotOfWGStoreView (v : WGStoreView) : Store PeerId :=
  ⟨v.peerCounter, fun i => (v.dev.bind fun d => d.peers[i]?).map (·.internalId)⟩

theorem samePeerSnapshot_of_sameWGStore (h : SameWGStore a) : SamePeerSnapshot a :=
  h.of_factor snapshotOfWGStoreView snapshot (fun _ => rfl)

theorem SamePeerSnapshot.wp (h : SamePeerSnapshot a) (P : Store PeerId → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ a ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  ProjectedAction.wp h P (fun _ _ he hp => he ▸ hp)

theorem samePeerSnapshot_of_wp (a : WG.M α)
    (h : ∀ s, ⦃fun w => ⌜snapshot w = s⌝⦄ a
      ⦃⇓? _ w => ⌜snapshot w = s⌝⦄) : SamePeerSnapshot a :=
  ProjectedAction.of_wp snapshot (fun s t => t = s) a h

theorem getPeer_live_spec (P : Store PeerId → Prop) (i : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ getPeer i
    ⦃⇓? p w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some p.internalId⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p w' ambient' hp hr
  obtain ⟨rfl, _, hi⟩ := getPeer_current i w w' p ambient ambient' hr
  exact ⟨hp, hi⟩

theorem setPeer_live_spec (P : Store PeerId → Prop) (i : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some p.internalId⌝⦄ setPeer i p
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases x
  rw [setPeer_same i p w w' ambient ambient' hp.2 hr]
  exact hp.1

theorem modifyDev_peer_spec (P : Store PeerId → Prop) (f : Device → Device)
    (hf : ∀ d, (f d).peers = d.peers) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [snapshot, modifyDev, Option.bind_map, Function.comp_def, hf] using hp

theorem requireNotPending_samePeerSnapshot (pid : PeerId) (what : String) :
    SamePeerSnapshot (requireNotPending pid what) := by
  apply samePeerSnapshot_of_wp
  intro s
  mvcgen [requireNotPending]
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
    refcountIncNotZero, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    unsupported, invariant, AmbientM.unsupported, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [snapshot]

theorem dstCacheReset_samePeerSnapshot (pid : PeerId) : SamePeerSnapshot (dstCacheReset pid) := by
  apply samePeerSnapshot_of_wp
  intro s
  have get_spec := getPeer_live_spec (fun t => t = s)
  have set_spec := setPeer_live_spec (fun t => t = s)
  have ambient_spec (α : Type) (a : AmbientM α) :
      ⦃fun w => ⌜snapshot w = s⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ w => ⌜snapshot w = s⌝⦄ :=
    hoare_liftAmbient a (fun w => snapshot w = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, dstCacheReset, getAmbient,
    hiddenJiffies, get_spec, set_spec, ambient_spec]
  all_goals simp_all

theorem resetLastSentHandshake_samePeerSnapshot (pid : PeerId) :
    SamePeerSnapshot (resetLastSentHandshake pid) := by
  apply samePeerSnapshot_of_wp
  intro s
  have get_spec := getPeer_live_spec (fun t => t = s)
  have set_spec := setPeer_live_spec (fun t => t = s)
  have ambient_spec (α : Type) (a : AmbientM α) :
      ⦃fun w => ⌜snapshot w = s⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ w => ⌜snapshot w = s⌝⦄ :=
    hoare_liftAmbient a (fun w => snapshot w = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, resetLastSentHandshake,
    hiddenClock64, get_spec, set_spec, ambient_spec]
  all_goals simp_all

theorem precomputeStaticStatic_samePeerSnapshot (pid : PeerId) :
    SamePeerSnapshot (precomputeStaticStatic pid) := by
  apply samePeerSnapshot_of_wp
  intro s
  have get_spec := getPeer_live_spec (fun t => t = s)
  have set_spec := setPeer_live_spec (fun t => t = s)
  have pending_spec := requireNotPending_peer_spec (fun t => t = s)
  mvcgen [precomputeStaticStatic, pending_spec, get_spec, set_spec,
    getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [snapshot]

theorem handshakeInit_samePeerSnapshot (pid : PeerId) (psk : Option Key) :
    SamePeerSnapshot (handshakeInit pid psk) := by
  apply samePeerSnapshot_of_wp
  intro s
  have get_spec := getPeer_live_spec (fun t => t = s)
  have set_spec := setPeer_live_spec (fun t => t = s)
  have precompute_spec := (precomputeStaticStatic_samePeerSnapshot pid).wp (fun t => t = s)
  mvcgen [handshakeInit, IndexOwner.setPeerWord, get_spec, set_spec, precompute_spec,
    branch, AmbientM.branch]
  all_goals simp_all [snapshot]

end Leanux.Proofs.WG.Peers
