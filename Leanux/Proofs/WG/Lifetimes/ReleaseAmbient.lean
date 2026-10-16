import Leanux.Proofs.WG.Lifetimes.DecryptWorker
import Leanux.Proofs.WG.Lifetimes.ReleaseInvariant

/-! The stronger release invariant instantiates the same enqueue/decrypt
caller proofs. Callback contracts retain resident uniqueness; no allocation
or concrete scheduler coverage is inferred from this instantiation. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem releaseFromMixed {S α : Type} {project : S → WGWorld}
    {g : PrefixT LifetimeEvent S α} {P : IdentityView → Prop} {Q : α → IdentityView → Prop}
    (hg : ProjectedAmbientSpec project (fun h w => MixedInv h (project w))
      (fun s => ReleaseUnique s ∧ P s) g (fun x s => ReleaseUnique s ∧ Q x s)) :
    ProjectedAmbientSpec project (fun h w => ReleaseInv h (project w)) P g Q :=
  hg.consequence (fun _ _ hi => ⟨hi.1.1, hi.1.2, hi.2⟩)
    (fun _ _ _ hi => ⟨⟨hi.1, hi.2.1⟩, hi.2.2⟩)

theorem releaseFromMixedState
    (hg : MixedSpec (fun s => ReleaseUnique s ∧ P s) g
      (fun x s => ReleaseUnique s ∧ Q x s)) : AmbientSpec ReleaseInv P g Q :=
  hg.consequence (fun _ _ _ hi => ⟨hi.1.1, hi.1.2, hi.2⟩)
    (fun _ _ _ _ hi => ⟨⟨hi.1, hi.2.1⟩, hi.2.2⟩)

theorem releasePeerFrame {S α : Type} {project : S → WGWorld}
    {g : PrefixT LifetimeEvent S α} {a : StateT S (Except Stop) α}
    (hg : PrefixPreserves (fun h w => MixedInv h (project w)) LifetimeEvent.Safe g)
    (he : ErasesPrefix g a) (hv : SameView (otherResidents ∘ project) a) :
    PrefixPreserves (fun h w => ReleaseInv h (project w)) LifetimeEvent.Safe g :=
  (PrefixEnsures.frameView
      (show PrefixEnsures (fun h w => MixedInv h (project w)) LifetimeEvent.Safe g
        (fun _ h w => MixedInv h (project w)) from hg)
      he (otherResidents ∘ project) hv
      (fun s => ResidentUnique s.1 ∧ ResidentUnique s.2)).preserves

theorem releasePeerStateFrame {g : MixedM α} {a : WG.M α}
    (hg : StatePrefixPreserves (fun h w _ => MixedInv h w) LifetimeEvent.Safe g)
    (he : ErasesStatePrefix g a) (hv : SameView otherResidents a) :
    StatePrefixPreserves (fun h w _ => ReleaseInv h w) LifetimeEvent.Safe g := by
  intro w ambient h hi
  obtain ⟨suffix, hsuf, hsafe, hout⟩ := hg w ambient h hi.1
  refine ⟨suffix, hsuf, hsafe, ?_⟩
  cases hr : (runPrefix (g.run w) ambient h).1 with
  | error e => trivial
  | ok out =>
    rcases out with ⟨⟨x, v⟩, ambient'⟩
    have hv' := (ProjectedAction.iff_run_ambient _ _ _).mp hv
      w ambient x v ambient' ((he w ambient h).symm.trans hr)
    have hu : ReleaseUnique (identityView v) := by
      change ResidentUnique (otherResidents v).1 ∧ ResidentUnique (otherResidents v).2
      rw [hv']
      exact hi.2
    exact ⟨by simpa only [hr] using hout, hu⟩

theorem releaseAmbient : AmbientContracts ReleaseInv where
  safe := fun _ _ hi => hi.safe
  storeStable := by
    intro h w v he hi
    have hv : identityView v = identityView w := by
      have hd := congrArg WGStoreView.dev he
      have hc := congrArg WGStoreView.peerCounter he
      simp only [wgStoreView] at hd hc
      unfold identityView Peers.snapshot keypairResidents packetResidents
      rw [hd, hc]
    exact ⟨hi.1.congr hv, hv ▸ hi.2⟩
  getPeer := by
    intro P id
    apply releaseFromMixedState
    exact mixed_state_forget (mixed_getPeer (fun s => ReleaseUnique s ∧ P s) id)
      (fun _ _ hi => ⟨hi.1.1, hi.1.2, hi.2⟩)
  getKeypair := by
    intro P id
    apply releaseFromMixedState
    exact mixed_state_forget (mixed_getKeypair (fun s => ReleaseUnique s ∧ P s) id)
      (fun _ _ hi => ⟨hi.1.1, hi.1.2, hi.2⟩)
  getRx := by
    intro P id
    apply releaseFromMixedState
    exact mixed_state_forget (mixed_getRxSkb (fun s => ReleaseUnique s ∧ P s) id)
      (fun _ _ hi => ⟨hi.1.1, hi.1.2, hi.2⟩)
  setPeer := by
    intro P id p
    apply releaseFromMixedState
    exact (mixed_setPeer (fun s => ReleaseUnique s ∧ P s) id p).consequence
      (fun _ _ _ hi => ⟨hi.1, ⟨hi.2.1, hi.2.2.1⟩, hi.2.2.2⟩)
      (fun _ _ _ _ hi => hi)
  setKeypair := by
    intro P id k
    apply releaseFromMixedState
    exact (mixed_setKeypair (fun s => ReleaseUnique s ∧ P s) id k).consequence
      (fun _ _ _ hi => ⟨hi.1, ⟨hi.2.1, hi.2.2.1⟩, hi.2.2.2⟩)
      (fun _ _ _ _ hi => hi)
  setRx := fun P id f => releaseFromMixedState (mixed_setRxSkb (fun s => ReleaseUnique s ∧ P s) id f)
  peerGet := fun id => releasePeerStateFrame (peerGetMixed_preserves id)
    (peerGetMixed_erases id) (peerGet_otherResidents id)
  peerPut := fun id => releasePeerStateFrame (peerPutMixed_preserves id)
    (peerPutMixed_erases id) (peerPut_otherResidents id)

theorem decryptQueue_release (ring : PtrRing SkbId) :
    StatePrefixPreserves (fun h w _ => ReleaseInv h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with decryptQueue := ring})) :=
  AmbientContracts.drop (Q := fun _ _ => True) (releaseFromMixedState
    (mixed_state_lift (fun s => ReleaseUnique s ∧ True) _ (decryptQueue_identity ring)))

theorem enqueuePerPeerRxPrefix_release
    (hi : PrefixPreserves (fun h w => ReleaseInv h w.wg) LifetimeEvent.Safe irq) (id : SkbId) (state : PacketState) :
    PrefixPreserves (fun h w => ReleaseInv h w.wg) LifetimeEvent.Safe (enqueuePerPeerRxPrefix irq id state) :=
  enqueuePerPeerRxPrefix_preserves_ambient (ProductAmbientContracts.ofNative releaseAmbient) hi id state

theorem decryptPacketPrefix_release (pkt : RxPacket) :
    StatePrefixPreserves (fun h w _ => ReleaseInv h w) LifetimeEvent.Safe (decryptPacketPrefix pkt) :=
  AmbientContracts.drop (decryptPacketPrefix_spec_ambient releaseAmbient (fun _ => True) pkt)

theorem decryptIterPrefix_release
    (hs : PrefixPreserves (fun h w => ReleaseInv h w.wg) LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves (fun h w => ReleaseInv h w.wg) LifetimeEvent.Safe irq)
    (hr : PrefixPreserves (fun h w => ReleaseInv h w.wg) LifetimeEvent.Safe needResched) :
    PrefixPreserves (fun h w => ReleaseInv h w.wg) LifetimeEvent.Safe (decryptIterPrefix softirq irq needResched) :=
  decryptIterPrefix_preserves_ambient (ProductAmbientContracts.ofNative releaseAmbient)
    (fun ring => (decryptQueue_release ring).liftWGObserver) hs hi hr

end Leanux.Proofs.WG.Lifetimes
