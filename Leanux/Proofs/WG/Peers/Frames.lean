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

theorem samePeerSnapshot_of_sameWGStore
    {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : SameView (fun s => wgStoreView (project s)) a) :
    SameView (fun s => snapshot (project s)) a :=
  h.of_factor snapshotOfWGStoreView (fun s => snapshot (project s)) (fun _ => rfl)

theorem samePeerSnapshot_of_wp
    {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Store PeerId}
    (a : StateT S m α)
    (h : ∀ initial, ⦃fun w => ⌜project w = initial⌝⦄ a
      ⦃⇓? _ w => ⌜project w = initial⌝⦄) : SameView project a :=
  SameView.of_wp project a h

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

  exact SameView.pure snapshot ()

theorem requireNotPending_peer_spec (P : Store PeerId → Prop) (pid : PeerId) (what : String) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ requireNotPending pid what
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  SameView.wp (requireNotPending_samePeerSnapshot pid what) P

theorem peerGetMaybeZero_samePeerSnapshot (peer : Option PeerId) :
    SamePeerSnapshot (peerGetMaybeZero peer) := by

  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result out ambient' hr
  cases peer with
  | none =>
    simp [peerGetMaybeZero, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, hd, branch,
        AmbientM.branch, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, hd, hp, branch,
          AmbientM.branch, invariant, AmbientM.invariant] at hr
        cases hr
      | some p =>
        by_cases zero : p.refcount = 0 <;> by_cases overflow : 2147483647 ≤ p.refcount <;>
          simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, setPeer, modifyDev,
            refcountIncNotZero, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
            hd, hp, zero, overflow, unsupported, AmbientM.unsupported] at hr
        all_goals try solve | cases hr
        all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        all_goals first
          | rfl
          | (simp only [snapshot, hd, Option.bind_some]
             exact mapStore_insert_same _ _ _ p _ hp rfl)

theorem dstCacheReset_samePeerSnapshot (pid : PeerId) : SamePeerSnapshot (dstCacheReset pid) := by

  apply samePeerSnapshot_of_wp
  intro s
  let P := fun w : WGWorld => snapshot w = s
  have ambient {α : Type} (a : AmbientM α) : Preserves P (StateT.lift a) :=
    hoare_liftAmbient a P
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  unfold dstCacheReset
  apply preserves_bind (ambient (get : AmbientM Ambient))
  intro a
  apply preserves_bind read
  intro w
  split
  · exact preserves_pure _
  · apply preserves_bind (ambient (AmbientM.hiddenJiffies .dstCacheResetTs))
    intro ts
    apply hoare_bind _ _ (getPeer_live_spec (fun t => t = s) pid)
    intro p
    exact setPeer_live_spec (fun t => t = s) pid _

theorem resetLastSentHandshake_samePeerSnapshot (pid : PeerId) :
    SamePeerSnapshot (resetLastSentHandshake pid) := by

  apply samePeerSnapshot_of_wp
  intro s
  unfold resetLastSentHandshake
  apply preserves_bind (hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent)
    (fun w => snapshot w = s))
  intro now
  apply hoare_bind _ _ (getPeer_live_spec (fun t => t = s) pid)
  intro p
  exact setPeer_live_spec (fun t => t = s) pid _

theorem precomputeStaticStatic_samePeerSnapshot (pid : PeerId) :
    SamePeerSnapshot (precomputeStaticStatic pid) := by

  apply samePeerSnapshot_of_wp
  intro s
  let P := fun w : WGWorld => snapshot w = s
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Preserves Q (StateT.lift a) := hoare_liftAmbient a Q
  have device : Preserves P getDev := by
    unfold getDev
    apply preserves_bind (hoare_consequence (hoare_get P)
      (fun _ h => h) (fun _ _ h => h.2))
    intro w
    cases w.dev
    · exact ambient (AmbientM.invariant "no WireGuard device in this trace's fixture") P
    · exact preserves_pure _
  have clear : Preserves P (do
      let current ← getPeer pid
      setPeer pid {current with precomputedStaticStatic := List.replicate 32 0}) := by
    apply hoare_bind _ _ (getPeer_live_spec (fun t => t = s) pid)
    intro current
    exact setPeer_live_spec (fun t => t = s) pid _
  simp only [precomputeStaticStatic, requireNotPending, pure_bind]
  apply hoare_bind _ _ device
  intro d
  apply hoare_bind _ _ (getPeer_live_spec (fun t => t = s) pid)
  intro p
  apply hoare_bind _ _ (ambient (AmbientM.branch .precomputeNoIdentity !d.staticIdentity.hasIdentity)
    (fun w => P w ∧ (snapshot w).slots pid = some p.internalId))
  intro noIdentity
  cases noIdentity with
  | true =>
    exact hoare_consequence clear (fun _ h => h.1) (fun _ _ h => h)
  | false =>
    apply hoare_bind _ _ (setPeer_live_spec (fun t => t = s) pid _)
    intro _
    apply preserves_bind (ambient (AmbientM.branch .precomputeNullPoint
      !(curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2) P)
    intro zero
    cases zero
    · exact preserves_pure _
    · exact clear

theorem handshakeInit_samePeerSnapshot (pid : PeerId) (psk : Option Key) :
    SamePeerSnapshot (handshakeInit pid psk) := by

  apply samePeerSnapshot_of_wp
  intro s
  let P := fun w : WGWorld => snapshot w = s
  have init : Preserves P (IndexOwner.setPeerWord (.handshake pid) (some pid)) := by
    unfold IndexOwner.setPeerWord
    apply hoare_bind _ _ (getPeer_live_spec (fun t => t = s) pid)
    intro p
    exact setPeer_live_spec (fun t => t = s) pid _
  have tail := SameView.wp (precomputeStaticStatic_samePeerSnapshot pid) (fun t => t = s)
  unfold handshakeInit
  apply preserves_bind init
  intro _
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .handshakeInitHasPsk psk.isSome) P)
  intro keyed
  cases keyed with
  | false => exact tail
  | true =>
    apply hoare_bind _ _ (getPeer_live_spec (fun t => t = s) pid)
    intro p
    apply hoare_bind _ _ (setPeer_live_spec (fun t => t = s) pid _)
    intro _
    exact tail

end Leanux.Proofs.WG.Peers
