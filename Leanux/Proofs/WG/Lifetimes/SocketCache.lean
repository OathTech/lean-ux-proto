import Leanux.Proofs.WG.Lifetimes.LoopbackAccess

/-! Complete cache and endpoint-source calls. The cache-get flag guard precedes
its peer read; a miss retains its read if the subsequent clock record fails. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def dstCacheResetNowPrefix (pid : PeerId) : MixedM Unit := do
  dstCacheResetMixed pid
  modifyPeerKeysPrefix pid fun p => {p with dstCache := {p.dstCache with slot := none}}

def clearPeerEndpointSrcPrefix (pid : PeerId) : MixedM Unit := do
  modifyPeerKeysPrefix pid fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}}
  dstCacheResetNowPrefix pid

def dstCacheSetPrefix (pid : PeerId) (src gen dev : Nat) : MixedM Unit :=
  modifyPeerKeysPrefix pid fun p => {p with dstCache := {p.dstCache with slot := some {src,gen,dev}}}

def dstCacheGetPrefix (pid : PeerId) (gen : Nat) : MixedM (Option DstSlot) := do
  let a ← liftWGPrefix (getAmbient : WG.M Ambient)
  let w ← liftWGPrefix (get : WG.M WGWorld)
  if !(a.armRecords && w.dstCacheRecords) then return none
  let p ← getPeerMixed pid
  let c := p.dstCache
  if let some s := c.slot then
    if timeAfter c.refreshTs c.resetTs && s.gen == gen then return some s
  let ts ← liftWGPrefix (hiddenJiffies .dstCacheRefreshTs)
  setPeerMixed pid {p with dstCache := {c with slot := none, refreshTs := ts}}
  return none

theorem dstCacheResetNowPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (dstCacheResetNowPrefix pid) (dstCacheResetNow pid) := by
  exact erasesStatePrefix_bind (dstCacheResetMixed_erases pid) (fun _ => modifyPeerKeysPrefix_erases _ _)

theorem clearPeerEndpointSrcPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (clearPeerEndpointSrcPrefix pid) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrcPrefix clearPeerEndpointSrc modifyPeerKeysPrefix
  simp only [bind_assoc]
  exact erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ =>
    erasesStatePrefix_bind (setPeerMixed_erases _ _) (fun _ => dstCacheResetNowPrefix_erases _))

theorem dstCacheSetPrefix_erases (pid : PeerId) (src gen dev : Nat) :
    ErasesStatePrefix (dstCacheSetPrefix pid src gen dev) (dstCacheSet pid src gen dev) :=
  modifyPeerKeysPrefix_erases _ _

theorem dstCacheGetPrefix_erases (pid : PeerId) (gen : Nat) :
    ErasesStatePrefix (dstCacheGetPrefix pid gen) (dstCacheGet pid gen) := by
  unfold dstCacheGetPrefix dstCacheGet
  repeat' first
    | exact getPeerMixed_erases _
    | exact setPeerMixed_erases _ _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | split
    | (intro x; try dsimp only)
  all_goals simp_all [StateT.run_pure]

theorem dstCacheResetNowPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (dstCacheResetNowPrefix pid) (fun _ => P) :=
  StatePrefixEnsures.bind (dstCacheResetMixed_spec c P pid)
    (fun _ => modifyPeerKeysPrefix_spec_ambient c P pid _ (fun _ => rfl))

theorem clearPeerEndpointSrcPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (clearPeerEndpointSrcPrefix pid) (fun _ => P) :=
  StatePrefixEnsures.bind (modifyPeerKeysPrefix_spec_ambient c P pid _ (fun _ => rfl))
    (fun _ => dstCacheResetNowPrefix_spec c P pid)

theorem dstCacheSetPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) (src gen dev : Nat) :
    AmbientSpec I P (dstCacheSetPrefix pid src gen dev) (fun _ => P) :=
  modifyPeerKeysPrefix_spec_ambient c P pid _ (fun _ => rfl)

theorem dstCacheGetPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) (gen : Nat) :
    AmbientSpec I P (dstCacheGetPrefix pid gen) (fun _ => P) := by
  unfold dstCacheGetPrefix
  apply StatePrefixEnsures.bind (c.store P (getAmbient : WG.M Ambient)
    (by intro initial; exact hoare_liftAmbient (get : AmbientM Ambient) _))
  intro a
  apply StatePrefixEnsures.bind (c.store P (get : WG.M WGWorld)
    (by intro initial; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)))
  intro w
  split
  · exact c.pure P _
  · apply StatePrefixEnsures.bind (c.getPeer P pid)
    intro p
    have miss : AmbientSpec I (fun s => P s ∧ s.1.slots pid = some p.internalId)
        (do let ts ← liftWGPrefix (hiddenJiffies .dstCacheRefreshTs)
            setPeerMixed pid {p with dstCache := {p.dstCache with slot := none, refreshTs := ts}}
            pure (none : Option DstSlot)) (fun _ => P) := by
      exact StatePrefixEnsures.bind (c.store (fun s => P s ∧ s.1.slots pid = some p.internalId)
        (hiddenJiffies .dstCacheRefreshTs)
        (by intro initial; exact hoare_liftAmbient (AmbientM.hiddenJiffies .dstCacheRefreshTs) _))
        (fun ts => StatePrefixEnsures.bind (c.setPeer P pid {p with dstCache := {p.dstCache with slot := none, refreshTs := ts}})
          (fun _ => c.pure P (none : Option DstSlot)))
    dsimp only
    split
    · split
      · exact (c.pure (fun s => P s ∧ s.1.slots pid = some p.internalId) _).consequence (fun _ _ _ hi => hi) (fun _ _ _ _ hi => ⟨hi.1, hi.2.1⟩)
      · exact miss
    · exact miss

theorem dstCacheResetNowPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    ProductAmbientSpec I P (liftWGObserver (dstCacheResetNowPrefix pid)) (fun _ => P) := by
  simp only [dstCacheResetNowPrefix, liftWGObserver_bind]
  exact PrefixEnsures.bind (dstCacheResetMixed_spec_product c P pid)
    (fun _ => modifyPeerKeysPrefix_spec_product c P pid _ (fun _ => rfl))

theorem clearPeerEndpointSrcPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    ProductAmbientSpec I P (liftWGObserver (clearPeerEndpointSrcPrefix pid)) (fun _ => P) := by
  simp only [clearPeerEndpointSrcPrefix, liftWGObserver_bind]
  exact PrefixEnsures.bind (modifyPeerKeysPrefix_spec_product c P pid _ (fun _ => rfl))
    (fun _ => dstCacheResetNowPrefix_spec_product c P pid)

theorem dstCacheSetPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (src gen dev : Nat) :
    ProductAmbientSpec I P (liftWGObserver (dstCacheSetPrefix pid src gen dev)) (fun _ => P) :=
  modifyPeerKeysPrefix_spec_product c P pid _ (fun _ => rfl)

theorem dstCacheGetPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) (gen : Nat) :
    ProductAmbientSpec I P (liftWGObserver (dstCacheGetPrefix pid gen)) (fun _ => P) := by
  unfold dstCacheGetPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (c.nativeStore P (getAmbient : WG.M Ambient)
    (by intro initial; exact hoare_liftAmbient (get : AmbientM Ambient) _))
  intro a
  apply PrefixEnsures.bind (c.nativeStore P (get : WG.M WGWorld)
    (by intro initial; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)))
  intro w
  split
  · exact c.pure P _
  · apply PrefixEnsures.bind (c.getPeer P pid)
    intro p
    have miss : ProductAmbientSpec I (fun s => P s ∧ s.1.slots pid = some p.internalId)
        (liftWGObserver (do let ts ← liftWGPrefix (hiddenJiffies .dstCacheRefreshTs)
                            setPeerMixed pid {p with dstCache := {p.dstCache with slot := none, refreshTs := ts}}
                            pure (none : Option DstSlot))) (fun _ => P) := by
      simp only [liftWGObserver_bind, liftWGObserver_pure]
      exact PrefixEnsures.bind (c.nativeStore (fun s => P s ∧ s.1.slots pid = some p.internalId)
        (hiddenJiffies .dstCacheRefreshTs)
        (by intro initial; exact hoare_liftAmbient (AmbientM.hiddenJiffies .dstCacheRefreshTs) _))
        (fun ts => PrefixEnsures.bind (c.setPeer P pid {p with dstCache := {p.dstCache with slot := none, refreshTs := ts}})
          (fun _ => c.pure P (none : Option DstSlot)))
    dsimp only
    split
    · simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
      split
      · exact (c.pure (fun s => P s ∧ s.1.slots pid = some p.internalId) _).consequence
          (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
      · simpa only [liftWGObserver_bind, liftWGObserver_pure] using miss
    · simpa only [liftWGObserver_bind, liftWGObserver_pure] using miss

end Leanux.Proofs.WG.Lifetimes
