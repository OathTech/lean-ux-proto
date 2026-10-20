import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointCanonicalFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorSource

/-! Fixed cache-source witnesses expose cached peer reads, clock inputs and
native slot writes. The frame requirements are proved separately from the
actual getter; they are not hypotheses of the source-point relation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketCache
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Prepare.Points

noncomputable def ambientShape (body : AmbientM α) : Shape (liftWGPrefix (monadLift body : WG.M α) : MixedM α) :=
  .quiet _ (fun initial=>Leanux.Proofs.Framing.hoare_liftAmbient body (fun w=>StagedEntry.view w=initial))

noncomputable def peerRead (pid : PeerId) : Shape (getPeerMixed pid) :=
  .focus _ _ (fun _=>rfl) (.access (.readPeer pid))

noncomputable def peerWrite (pid : PeerId) (p : Peer) : Shape (setPeerMixed pid p) :=
  .focus _ _ (fun _=>rfl) (.access (.writePeer pid p))

noncomputable def update (pid : PeerId) (f : Peer → Peer) : Shape (modifyPeerKeysPrefix pid f) :=
  .bind (peerRead pid) (fun p=>peerWrite pid (f p))

def miss (pid : PeerId) (p : Peer) : MixedM (Option DstSlot) := do
  let ts ← liftWGPrefix (hiddenJiffies .dstCacheRefreshTs)
  setPeerMixed pid {p with dstCache:={p.dstCache with slot:=none,refreshTs:=ts}}
  pure none

def afterRead (pid : PeerId) (gen : Nat) (p : Peer) : MixedM (Option DstSlot) := do
  if let some slot := p.dstCache.slot then
    if timeAfter p.dstCache.refreshTs p.dstCache.resetTs && slot.gen==gen then return some slot
  miss pid p

def getBody (pid : PeerId) (gen : Nat) : MixedM (Option DstSlot) := do
  let ambient ← liftWGPrefix (getAmbient : WG.M Ambient)
  let world ← liftWGPrefix (get : WG.M WGWorld)
  if !(ambient.armRecords && world.dstCacheRecords) then return none
  let p ← getPeerMixed pid
  afterRead pid gen p

theorem get_source (pid : PeerId) (gen : Nat) : dstCacheGetPrefix pid gen=getBody pid gen := rfl

theorem afterRead_source (pid : PeerId) (gen : Nat) (p : Peer) :
    afterRead pid gen p=(match p.dstCache.slot with
      | none=>miss pid p
      | some slot=>if timeAfter p.dstCache.refreshTs p.dstCache.resetTs && slot.gen==gen then pure (some slot) else miss pid p) := by
  unfold afterRead
  cases p.dstCache.slot <;> rfl

noncomputable def missShape (pid : PeerId) (p : Peer) : Shape (miss pid p) := by
  unfold miss
  apply Shape.bind (ambientShape (AmbientM.hiddenJiffies .dstCacheRefreshTs))
  intro ts
  exact .bind (peerWrite pid {p with dstCache:={p.dstCache with slot:=none,refreshTs:=ts}})
    (fun _=>.pure none)

noncomputable def afterReadShape (pid : PeerId) (gen : Nat) (p : Peer) : Shape (afterRead pid gen p) := by
  let shaped := optionShape p.dstCache.slot (miss pid p)
    (fun slot=>if timeAfter p.dstCache.refreshTs p.dstCache.resetTs && slot.gen==gen then pure (some slot) else miss pid p)
    (missShape pid p) (fun slot=>boolShape _ _ _ (.pure (some slot)) (missShape pid p))
  let source {action : MixedM (Option DstSlot)} (_ : Shape action) := action
  refine (congrArg Shape (show afterRead pid gen p=source shaped from ?_)).mpr shaped
  dsimp only [source]
  rw [afterRead_source]
  cases p.dstCache.slot <;> rfl

noncomputable def getShape (pid : PeerId) (gen : Nat) : Shape (dstCacheGetPrefix pid gen) := by
  change Shape (getBody pid gen)
  unfold getBody
  apply Shape.bind (ambientShape (get : AmbientM Ambient))
  intro ambient
  apply Shape.bind
  · prepare_shape_step
  intro world
  exact boolShape _ _ _ (.pure none) (.bind (peerRead pid) (afterReadShape pid gen))

noncomputable def setShape (pid : PeerId) (src gen dev : Nat) : Shape (dstCacheSetPrefix pid src gen dev) :=
  update pid (fun p=>{p with dstCache:={p.dstCache with slot:=some {src,gen,dev}}})

noncomputable def resetShape (pid : PeerId) : Shape (dstCacheResetMixed pid) := by
  unfold dstCacheResetMixed
  apply Shape.bind (ambientShape (get : AmbientM Ambient))
  intro ambient
  apply Shape.bind
  · prepare_shape_step
  intro world
  exact boolShape _ _ _ (.pure ()) (.bind (ambientShape (AmbientM.hiddenJiffies .dstCacheResetTs))
    (fun ts=>update pid (fun p=>{p with dstCache:={p.dstCache with resetTs:=ts}})))

noncomputable def clear4Shape (cache : Option PeerId) : Shape (send4ClearSrcPrefix cache) := by
  cases cache with
  | none=>exact .pure ()
  | some pid=>exact update pid (fun p=>{p with endpoint:=p.endpoint.map fun e=>{e with src:=0,srcIf:=0}})

noncomputable def clear6Shape (cache : Option PeerId) : Shape (SocketInterior.Six.clear cache) := by
  cases cache with
  | none=>exact .pure ()
  | some pid=>exact update pid (fun p=>{p with endpoint:=p.endpoint.map fun e=>{e with src:=0}})

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketCache
