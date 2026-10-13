import Leanux.Proofs.WG.Lifetimes.DecryptWorker
import Leanux.Proofs.WG.Lifetimes.ReleaseInvariant

/-! The stronger release invariant instantiates the same enqueue/decrypt
caller proofs. Callback contracts retain resident uniqueness; no allocation
or concrete scheduler coverage is inferred from this instantiation. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem releaseFromMixed
    (hg : MixedSpec (fun s => ReleaseUnique s ∧ P s) g
      (fun x s => ReleaseUnique s ∧ Q x s)) : AmbientSpec ReleaseInv P g Q :=
  hg.consequence (fun _ _ hi => ⟨hi.1.1, hi.1.2, hi.2⟩)
    (fun _ _ _ hi => ⟨⟨hi.1, hi.2.1⟩, hi.2.2⟩)

theorem releasePeerFrame (hg : PrefixPreserves MixedInv LifetimeEvent.Safe g)
    (he : ErasesPrefix g a) (hv : SameView otherResidents a) :
    PrefixPreserves ReleaseInv LifetimeEvent.Safe g :=
  (PrefixEnsures.frameView (show PrefixEnsures MixedInv LifetimeEvent.Safe g
      (fun _ => MixedInv) from hg) he otherResidents hv
      (fun s => ResidentUnique s.1 ∧ ResidentUnique s.2)).preserves

theorem releaseAmbient : AmbientContracts ReleaseInv where
  safe := fun _ _ hi => hi.safe
  kernelStable := by
    intro h w v he hi
    have hv : identityView v = identityView w := by
      unfold identityView Peers.snapshot keypairResidents packetResidents
      rw [he]
    exact ⟨hi.1.congr hv, hv ▸ hi.2⟩
  getPeer := by
    intro P id
    apply releaseFromMixed
    exact mixed_forget (mixed_getPeer (fun s => ReleaseUnique s ∧ P s) id)
      (fun _ _ hi => ⟨hi.1.1, hi.1.2, hi.2⟩)
  getKeypair := by
    intro P id
    apply releaseFromMixed
    exact mixed_forget (mixed_getKeypair (fun s => ReleaseUnique s ∧ P s) id)
      (fun _ _ hi => ⟨hi.1.1, hi.1.2, hi.2⟩)
  getRx := by
    intro P id
    apply releaseFromMixed
    exact mixed_forget (mixed_getRxSkb (fun s => ReleaseUnique s ∧ P s) id)
      (fun _ _ hi => ⟨hi.1.1, hi.1.2, hi.2⟩)
  setPeer := by
    intro P id p
    apply releaseFromMixed
    exact (mixed_setPeer (fun s => ReleaseUnique s ∧ P s) id p).consequence
      (fun _ _ hi => ⟨hi.1, ⟨hi.2.1, hi.2.2.1⟩, hi.2.2.2⟩)
      (fun _ _ _ hi => hi)
  setKeypair := by
    intro P id k
    apply releaseFromMixed
    exact (mixed_setKeypair (fun s => ReleaseUnique s ∧ P s) id k).consequence
      (fun _ _ hi => ⟨hi.1, ⟨hi.2.1, hi.2.2.1⟩, hi.2.2.2⟩)
      (fun _ _ _ hi => hi)
  setRx := fun P id f => releaseFromMixed (mixed_setRxSkb (fun s => ReleaseUnique s ∧ P s) id f)
  peerGet := fun id => releasePeerFrame (peerGetMixed_preserves id)
    (peerGetMixed_erases id) (peerGet_otherResidents id)
  peerPut := fun id => releasePeerFrame (peerPutMixed_preserves id)
    (peerPutMixed_erases id) (peerPut_otherResidents id)

theorem decryptQueue_release (ring : PtrRing SkbId) :
    PrefixPreserves ReleaseInv LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with decryptQueue := ring})) :=
  AmbientContracts.drop (releaseFromMixed
    (mixed_lift (fun s => ReleaseUnique s ∧ True) _ (decryptQueue_identity ring)))

theorem enqueuePerPeerRxPrefix_release
    (hi : PrefixPreserves ReleaseInv LifetimeEvent.Safe irq) (id : SkbId) (state : PacketState) :
    PrefixPreserves ReleaseInv LifetimeEvent.Safe (enqueuePerPeerRxPrefix irq id state) :=
  enqueuePerPeerRxPrefix_preserves_ambient releaseAmbient hi id state

theorem decryptPacketPrefix_release (pkt : RxPacket) :
    PrefixPreserves ReleaseInv LifetimeEvent.Safe (decryptPacketPrefix pkt) :=
  AmbientContracts.drop (decryptPacketPrefix_spec_ambient releaseAmbient (fun _ => True) pkt)

theorem decryptIterPrefix_release
    (hs : PrefixPreserves ReleaseInv LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves ReleaseInv LifetimeEvent.Safe irq)
    (hr : PrefixPreserves ReleaseInv LifetimeEvent.Safe needResched) :
    PrefixPreserves ReleaseInv LifetimeEvent.Safe (decryptIterPrefix softirq irq needResched) :=
  decryptIterPrefix_preserves_ambient releaseAmbient decryptQueue_release hs hi hr

end Leanux.Proofs.WG.Lifetimes
