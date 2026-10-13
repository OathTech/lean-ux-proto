import Leanux.Proofs.WG.Lifetimes.LoopbackAccess

/-! Complete cache and endpoint-source calls. The cache-get flag guard precedes
its peer read; a miss retains its read if the subsequent clock record fails. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def dstCacheResetNowPrefix (pid : PeerId) : MixedM Unit := do
  dstCacheResetMixed pid
  modifyPeerKeysPrefix pid fun p => {p with dstCache := {p.dstCache with slot := none}}

def clearPeerEndpointSrcPrefix (pid : PeerId) : MixedM Unit := do
  modifyPeerKeysPrefix pid fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}}
  dstCacheResetNowPrefix pid

def dstCacheSetPrefix (pid : PeerId) (src gen dev : Nat) : MixedM Unit :=
  modifyPeerKeysPrefix pid fun p => {p with dstCache := {p.dstCache with slot := some {src,gen,dev}}}

def dstCacheGetPrefix (pid : PeerId) (gen : Nat) : MixedM (Option DstSlot) := do
  let w ← liftPrefix (get : M World)
  if !(w.armRecords && w.dstCacheRecords) then return none
  let p ← getPeerMixed pid
  let c := p.dstCache
  if let some s := c.slot then
    if c.refreshTs > c.resetTs && s.gen == gen then return some s
  let ts ← liftPrefix (hiddenU64 .dstCacheRefreshTs)
  setPeerMixed pid {p with dstCache := {c with slot := none, refreshTs := ts}}
  return none

theorem dstCacheResetNowPrefix_erases (pid : PeerId) :
    ErasesPrefix (dstCacheResetNowPrefix pid) (dstCacheResetNow pid) := by
  exact erasesPrefix_bind (dstCacheResetMixed_erases pid) (fun _ => modifyPeerKeysPrefix_erases _ _)

theorem clearPeerEndpointSrcPrefix_erases (pid : PeerId) :
    ErasesPrefix (clearPeerEndpointSrcPrefix pid) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrcPrefix clearPeerEndpointSrc modifyPeerKeysPrefix
  simp only [bind_assoc]
  exact erasesPrefix_bind (getPeerMixed_erases _) (fun _ =>
    erasesPrefix_bind (setPeerMixed_erases _ _) (fun _ => dstCacheResetNowPrefix_erases _))

theorem dstCacheSetPrefix_erases (pid : PeerId) (src gen dev : Nat) :
    ErasesPrefix (dstCacheSetPrefix pid src gen dev) (dstCacheSet pid src gen dev) :=
  modifyPeerKeysPrefix_erases _ _

theorem dstCacheGetPrefix_erases (pid : PeerId) (gen : Nat) :
    ErasesPrefix (dstCacheGetPrefix pid gen) (dstCacheGet pid gen) := by
  unfold dstCacheGetPrefix dstCacheGet
  repeat' first
    | exact getPeerMixed_erases _
    | exact setPeerMixed_erases _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | split
    | (intro x; try dsimp only)
  all_goals simp_all [runPrefix_pure, StateT.run_pure]

theorem dstCacheResetNowPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (dstCacheResetNowPrefix pid) (fun _ => P) :=
  PrefixEnsures.bind (dstCacheResetMixed_spec c P pid)
    (fun _ => modifyPeerKeysPrefix_spec_ambient c P pid _ (fun _ => rfl))

theorem clearPeerEndpointSrcPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (clearPeerEndpointSrcPrefix pid) (fun _ => P) :=
  PrefixEnsures.bind (modifyPeerKeysPrefix_spec_ambient c P pid _ (fun _ => rfl))
    (fun _ => dstCacheResetNowPrefix_spec c P pid)

theorem dstCacheSetPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) (src gen dev : Nat) :
    AmbientSpec I P (dstCacheSetPrefix pid src gen dev) (fun _ => P) :=
  modifyPeerKeysPrefix_spec_ambient c P pid _ (fun _ => rfl)

theorem dstCacheGetPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) (gen : Nat) :
    AmbientSpec I P (dstCacheGetPrefix pid gen) (fun _ => P) := by
  unfold dstCacheGetPrefix
  apply PrefixEnsures.bind (c.kernel P get (by intro w x v hr; cases hr; rfl))
  intro w
  split
  · exact c.pure P _
  · apply PrefixEnsures.bind (c.getPeer P pid)
    intro p
    have miss : AmbientSpec I (fun s => P s ∧ s.1.slots pid = some p.internalId)
        (do let ts ← liftPrefix (hiddenU64 .dstCacheRefreshTs)
            setPeerMixed pid {p with dstCache := {p.dstCache with slot := none, refreshTs := ts}}
            pure (none : Option DstSlot)) (fun _ => P) := by
      exact PrefixEnsures.bind (c.kernel (fun s => P s ∧ s.1.slots pid = some p.internalId)
        (hiddenU64 .dstCacheRefreshTs) (Peers.hiddenU64_sameKernel _))
        (fun ts => PrefixEnsures.bind (c.setPeer P pid {p with dstCache := {p.dstCache with slot := none, refreshTs := ts}})
          (fun _ => c.pure P (none : Option DstSlot)))
    dsimp only
    split
    · split
      · exact (c.pure (fun s => P s ∧ s.1.slots pid = some p.internalId) _).consequence (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
      · exact miss
    · exact miss

end Leanux.Proofs.WG.Lifetimes
