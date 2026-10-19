import Leanux.Proofs.WG.RetirementSecurity.HolderRemovalConfiguration

/-! Bulk removal saves actual base occurrences, detaches them all, and pays
the saved occurrences in source order. Equal owner slots remain separate
charges; neither list uniqueness nor immediate allocation destruction is used. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderRemoval
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem free_points : SameView ownershipPointView WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  let observe := fun s : WGStoreView × (PeerId → Option Peer) =>
    ((fun id : KeypairId => (s.1.dev.bind fun d => d.keypairs[id]?).map fun k => (k.internalId,k.refcount)),
      s.1.dev.isSome,(fun pid => (s.2 pid).map peerOwnership),
      (fun id : SkbId => (s.1.dev.bind fun d => d.txSkbs[id]?).map (·.keypair)),
      (fun id : SkbId => (s.1.dev.bind fun d => d.rxSkbs[id]?).map (·.keypair)))
  have fields := congrArg observe kept
  have erased (p : Peer) : peerOwnership {p with allowedipsList := []} = peerOwnership p := rfl
  simp only [observe,AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,
    erased,wgStoreView,Option.map_map,Option.bind_map,Option.map_bind,
    Function.comp_def,Option.isSome_map] at fields
  apply Prod.ext
  · funext id
    simpa only [ownershipPointView,RetirementSecurity.keyReferenceView,RetirementSecurity.keyAt,
      Option.map_bind,Option.bind_map,Function.comp_def] using congrFun (congrArg Prod.fst fields) id
  · simpa only [ownershipPointView,ownershipAt,peerAt,packetKeyWords,
      Option.map_bind,Option.bind_map,Function.comp_def] using congrArg Prod.snd fields

theorem entry_points : SameView ownershipPointView BaseRemoval.entry := by
  unfold BaseRemoval.entry
  exact free_points.bind (fun _ => (ownershipPoints_kernel _ getDev_sameWGStore).bind
    (fun _ => SameView.pure _ _))

theorem entry_anchors : Preserves (SlotPeerReferences holders loans) BaseRemoval.entry := by
  unfold BaseRemoval.entry
  apply preserves_bind (SlotAnchors.frame
    (BaseRemoval.allowedipsFree_view.factor (fun s => s.1.1.1)) free_points)
  intro _
  apply preserves_bind
    (show Preserves (SlotPeerReferences holders loans) getDev from by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a d v b before run
      exact (DecryptCarrier.getDev_current a b run).1 ▸ before)
  intro _
  exact preserves_pure _

theorem saved_make_dead_points (dead : List PeerId) : SameView ownershipPointView
    (for pid in dead do
      _ ← branch .peerRemoveAllIter1 true
      peerMakeDead pid : WG.M Unit) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  apply preserves_bind
  · apply list_view_spec ownershipPointView (· = initial)
    intro pid u
    exact preserves_bind (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter1 true) _)
      (fun _ => preserves_bind ((makeDead_ownership pid).wp (· = initial))
        (fun _ => preserves_pure _))
  · intro _
    exact preserves_pure ()

theorem saved_make_dead (keys : HolderAccount temporary w)
    (peers : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) (a b : Ambient)
    (run : (((for pid in holders.base.map Owner.slot do
      _ ← branch .peerRemoveAllIter1 true
      peerMakeDead pid) : WG.M Unit).run w).run a = .ok (((),v),b)) :
    HolderDrain.Ready (holders.withoutBase []) carriers (holders.base ++ loans) temporary v := by
  obtain ⟨funded,stableAfter⟩ := saved_makeDead_funded peers stable a b run
  have points := (ProjectedAction.iff_run_ambient _ _ _).mp (saved_make_dead_points _)
    w a () v b run
  have effect := (pinned_const _private.Leanux.Proofs.WG.Queues.HolderBaseRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.mark_saved_effect)
    (holders.base.map Owner.slot) w v a b run
  have anchorsAfter : SlotPeerReferences (holders.withoutBase []) (holders.base ++ loans) v :=
    anchors.transport (congrArg (fun s => s.1.1) effect.1) points (by
      simp only [withoutBase,List.nil_append]
      exact List.Perm.refl _)
  exact HolderDrain.initial (keys.points points) funded stableAfter anchorsAfter

theorem saved_after_dead (saved : Reservations)
    (before : HolderDrain.Ready original carriers (saved ++ loans) temporary w) (a b : Ambient)
    (run : (((for pid in saved.map Owner.slot do
      _ ← branch .peerRemoveAllIter2 true
      peerRemoveAfterDead pid) : WG.M Unit).run w).run a = .ok (((),v),b)) :
    HolderDrain.Ready original carriers loans temporary v := by
  induction saved generalizing w a with
  | nil =>
    simp only [List.map_nil,List.forIn_nil] at run
    cases run
    exact before
  | cons o saved ih =>
    have factor : (for pid in (o :: saved).map Owner.slot do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead pid : WG.M Unit) = (do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead o.slot
        for pid in saved.map Owner.slot do
          _ ← branch .peerRemoveAllIter2 true
          peerRemoveAfterDead pid) := by
      simp only [List.map_cons,List.forIn_cons,bind_assoc,pure_bind]
    rw [factor,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨flag,read,c,decision,rest⟩ := run
    have same := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter2 true) (fun g => g=w))
      w a flag read c rfl decision
    subst read
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨ignored,paid,d,payment,rest⟩ := rest
    cases ignored
    exact ih (after_dead before c d payment).1 d rest

theorem all_peers (keys : HolderAccount temporary w)
    (peers : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) (a b : Ambient)
    (run : (peerRemoveAll.run w).run a = .ok (((),v),b)) :
    HolderDrain.Ready (holders.withoutBase []) carriers loans temporary v := by
  rw [BaseRemoval.peerRemoveAll_entry,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨dead,entered,c,entry,rest⟩ := run
  obtain ⟨saved,funded,stable⟩ := saved_entry_funded peers stable a c entry
  have keysEntered := keys.points ((ProjectedAction.iff_run_ambient _ _ _).mp entry_points w a dead entered c entry)
  have anchorsEntered := (hoare_iff_run_ambient _ _ _).mp entry_anchors w a dead entered c anchors entry
  subst dead
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨ignored,marked,d,mark,rest⟩ := rest
  cases ignored
  have markedReady := saved_make_dead (v := marked) keysEntered funded stable anchorsEntered c d (by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨PUnit.unit,marked,d,mark,rfl⟩)
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨flag,read,e,decision,rest⟩ := rest
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter1 false) (fun g => g=marked))
    marked d flag read e rfl decision
  subst read
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨ignored,paid,f,payment,rest⟩ := rest
  cases ignored
  have done := saved_after_dead (v := paid) holders.base markedReady e f (by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨PUnit.unit,paid,f,payment,rfl⟩)
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨last,read,g,decision,rest⟩ := rest
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter2 false) (fun state => state=paid))
    paid f last read g rfl decision
  subst read
  cases rest
  exact done

end Leanux.Proofs.WG.RetirementSecurity.HolderRemoval
