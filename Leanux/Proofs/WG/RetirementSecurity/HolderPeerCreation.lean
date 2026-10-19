import Leanux.Proofs.WG.RetirementSecurity.HolderPeerCreationCore

/-! Native peer allocation and initialization preserve the exact key ledger:
the fresh peer contributes an empty loan group and publication creates only
its separately funded peer reference. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderPeerCreation
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

/-- The original allocation guards retain the entry world. Only the actual
creation core and initializer can alter it on a normal successful path. -/
theorem source (P : WGWorld → Prop) (w : WGWorld) (key : Key) (psk : Option Key)
    (before : P w)
    (core : ∀ d,w.dev=some d → P (Peers.creationCoreWorld w d.nextPeer key))
    (finish : ∀ pid,Preserves P (BaseCreation.finish pid key psk)) :
    Hoare (peerCreate key psk) (fun u => u=w) (fun _ => P) := by
  have getter : Hoare getDev (fun u => u=w) (fun d u => u=w ∧ w.dev=some d) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u a d v b same run
    subst u
    obtain ⟨same,time,device⟩ := DecryptCarrier.getDev_current a b run
    exact ⟨same,device⟩
  rw [BaseCreation.peerCreate_factor]
  apply hoare_bind _ _ getter
  intro d
  let Start := fun u => u=w ∧ w.dev=some d
  have ambient {α : Type} (act : AmbientM α) : Preserves Start (monadLift act : WG.M α) :=
    hoare_liftAmbient act Start
  have failure : Hoare (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId)) Start (fun _ => P) := by
    apply hoare_consequence (hoare_pure _ Start)
    · exact fun _ h => h
    · intro _ u h
      exact h.2.1.symm ▸ before
  apply hoare_bind _ _ (ambient (AmbientM.branchCmp .peerCreateMaxPeers
    (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE))
  intro maxPeers
  cases maxPeers with
  | true => exact failure
  | false =>
    apply hoare_bind _ _ (ambient (AmbientM.hiddenAlloc .kmemCacheZallocPeer))
    intro allocated
    apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateNoMem !allocated))
    intro noMem
    cases noMem with
    | true => exact failure
    | false =>
      apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateDstCacheFail false))
      intro cacheFailed
      cases cacheFailed with
      | true => exact failure
      | false =>
        apply hoare_bind _ _ (show Hoare (Peers.peerCreateCore d.nextPeer key) Start (fun _ => P) from ?_)
        · intro _
          exact preserves_bind (finish d.nextPeer) (fun _ => preserves_pure _)
        · apply (hoare_iff_run_ambient _ _ _).mpr
          intro u a result v b entry run
          obtain ⟨rfl,device⟩ := entry
          rw [Peers.peerCreateCore_run] at run
          cases run
          exact core d device

theorem precompute_points (pid : PeerId) :
    SameView ownershipPointView (precomputeStaticStatic pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold precomputeStaticStatic requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' holder_handshake_step initial

theorem init_points (pid : PeerId) (psk : Option Key) :
    SameView ownershipPointView (handshakeInit pid psk) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold handshakeInit IndexOwner.setPeerWord
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head precomputeStaticStatic; exact (precompute_points _).wp (·=initial))
    | holder_handshake_step initial

theorem reset_points (pid : PeerId) : SameView ownershipPointView (resetLastSentHandshake pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold resetLastSentHandshake
  repeat' holder_handshake_step initial

theorem finish_points (pid : PeerId) (key : Key) (psk : Option Key) :
    SameView ownershipPointView (BaseCreation.finish pid key psk) := by
  unfold BaseCreation.finish ConfiguredIdentity.publishRow
  apply SameView.bind
    ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.dstCacheReset_ownership) pid)
  intro _
  apply SameView.bind (init_points pid psk)
  intro _
  apply SameView.bind (reset_points pid)
  intro _
  exact ownership_modifyDev _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem keys (key : Key) (psk : Option Key)
    (before : HolderAccount temporary w) (configured : ConfiguredIdentity.Inv w)
    (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v := by
  apply (hoare_iff_run_ambient _ _ _).mp
    (source (HolderAccount temporary) w key psk before
      (fun d device => before.peer_create_core configured device key) ?_) w a result v b rfl run
  intro pid
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro u a result v b entry run
  exact entry.points ((ProjectedAction.iff_run_ambient _ _ _).mp (finish_points pid key psk) u a result v b run)

end Leanux.Proofs.WG.RetirementSecurity.HolderPeerCreation
