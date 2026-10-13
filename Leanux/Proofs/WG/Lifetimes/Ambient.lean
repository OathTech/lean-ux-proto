import Leanux.Proofs.WG.Lifetimes.KeypairAccess
import Leanux.Proofs.WG.Lifetimes.Acquire

/-! Caller contracts separate a history-dependent ambient invariant from
temporary predicates about identities resolved by local getters. These laws
describe the named observers; source coverage remains a separate obligation. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

abbrev AmbientSpec (I : List LifetimeEvent → World → Prop)
    (P : IdentityView → Prop) (g : MixedM α) (Q : α → IdentityView → Prop) :=
  PrefixEnsures (fun h w => I h w ∧ P (identityView w)) LifetimeEvent.Safe g
    (fun x h w => I h w ∧ Q x (identityView w))

structure AmbientContracts (I : List LifetimeEvent → World → Prop) : Prop where
  safe : ∀ h w, I h w → LifetimeEvent.Safe h
  kernelStable : ∀ h w v, v.k = w.k → I h w → I h v
  getPeer : ∀ P id, AmbientSpec I P (getPeerMixed id)
    (fun p s => P s ∧ s.1.slots id = some p.internalId)
  getKeypair : ∀ P id, AmbientSpec I P (getKeypairPrefix id)
    (fun k s => P s ∧ s.2.1 id = some k.internalId)
  getRx : ∀ P id, AmbientSpec I P (getRxSkbPrefix id)
    (fun _ s => P s ∧ ∃ stamp, s.2.2 (.inr id) = some stamp)
  setPeer : ∀ P id p, AmbientSpec I (fun s => P s ∧ s.1.slots id = some p.internalId)
    (setPeerMixed id p) (fun _ => P)
  setKeypair : ∀ P id k, AmbientSpec I (fun s => P s ∧ s.2.1 id = some k.internalId)
    (setKeypairPrefix id k) (fun _ => P)
  setRx : ∀ P id f, AmbientSpec I P (setRxSkbPrefix id f) (fun _ => P)
  peerGet : ∀ id, PrefixPreserves I LifetimeEvent.Safe (peerGetMixed id)
  peerPut : ∀ id, PrefixPreserves I LifetimeEvent.Safe (peerPutMixed id)

namespace AmbientContracts

theorem pure (c : AmbientContracts I) (P : IdentityView → Prop) (x : α) :
    AmbientSpec I P (pure x) (fun _ => P) :=
  PrefixEnsures.pure (fun h w hi => c.safe h w hi.1) (fun _ _ hi => hi)

theorem forget (hg : AmbientSpec I P g Q) (hq : ∀ x s, Q x s → R x s) :
    AmbientSpec I P g R :=
  hg.consequence (fun _ _ hi => hi) (fun x _ _ hi => ⟨hi.1, hq x _ hi.2⟩)

theorem drop (hg : AmbientSpec I (fun _ => True) g Q) :
    PrefixPreserves I LifetimeEvent.Safe g :=
  (hg.consequence (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => hi.1)).preserves

/-- This transports state predicates for an explicitly chosen access-free
lift. SameKernel by itself is not a claim that an action has no reads. -/
theorem kernel (c : AmbientContracts I) (P : IdentityView → Prop)
    (a : M α) (ha : SameKernel a) : AmbientSpec I P (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a (fun h w hi => c.safe h w hi.1)
  intro h w x v hi hr
  exact ⟨c.kernelStable h w v (ha w x v hr) hi.1,
    (identity_sameKernel ha w x v hr) ▸ hi.2⟩

theorem branch (c : AmbientContracts I) (P : IdentityView → Prop) (d : Decision) (b : Bool) :
    AmbientSpec I P (liftPrefix (Leanux.branch d b)) (fun _ => P) :=
  c.kernel P _ (sameKernel_branch d b)

theorem invariant (c : AmbientContracts I) (P : IdentityView → Prop) (why : String) :
    AmbientSpec I P (liftPrefix (Leanux.invariant (α := α) why)) (fun _ => P) := by
  apply c.kernel
  intro w x v hr
  simp [Leanux.invariant] at hr

theorem getKeypair_frame (c : AmbientContracts I) (P : IdentityView → Prop) (id : KeypairId) :
    AmbientSpec I P (getKeypairPrefix id) (fun _ => P) :=
  forget (c.getKeypair P id) (fun _ _ hi => hi.1)

end AmbientContracts

theorem mixedAmbient : AmbientContracts MixedInv where
  safe := fun _ _ hi => hi.safe
  kernelStable := by
    intro h w v he hi
    apply hi.congr
    unfold identityView Peers.snapshot keypairResidents packetResidents
    rw [he]
  getPeer := mixed_getPeer
  getKeypair := mixed_getKeypair
  getRx := mixed_getRxSkb
  setPeer := mixed_setPeer
  setKeypair := mixed_setKeypair
  setRx := mixed_setRxSkb
  peerGet := peerGetMixed_preserves
  peerPut := peerPutMixed_preserves

end Leanux.Proofs.WG.Lifetimes
