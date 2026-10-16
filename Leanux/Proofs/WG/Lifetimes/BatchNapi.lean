import Leanux.Proofs.WG.Lifetimes.StackAccess
import Leanux.Proofs.WG.Lifetimes.SavedPeers
import Leanux.Proofs.Logged.PrefixBatch

/-! Exact NET_RX dispatch observations. Captured peer-map predicates are
observed before any poll callback can change the resident store. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def napiSoftirqPrefix : PrefixM LifetimeEvent Unit := do
  let d ← liftWGObserver (liftWGPrefix getDev)
  let pending ← liftWGObserver (savedPeerFilterMap (fun pid p => if p.napiScheduled then some pid else none) d.peers.toList)
  if pending.isEmpty then return
  if (← liftPrefix getAmbient).hidden.isSome && (← liftPrefix peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  if pending.length > 1 then liftPrefix (unsupported "NAPI polls of several peers in one softirq")
  runWorkerPrefix .netRx do
    for pid in pending do
      discard <| rxPollStackPrefix pid NAPI_POLL_WEIGHT

theorem napiSoftirqPrefix_erases : ErasesPrefix napiSoftirqPrefix Env.napiSoftirq := by
  unfold napiSoftirqPrefix Env.napiSoftirq
  apply erasesPrefix_bind (liftWGObserver_erases (erasesStatePrefix_lift _))
  intro d
  have h := liftWGObserver_erases (savedPeerFilterMap_erases (fun pid p => if p.napiScheduled then some pid else none) d.peers.toList)
  apply erasesPrefix_bind_pure h
  dsimp only
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible exact rxPollStackPrefix_erases _ _
    | with_reducible exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem napiSoftirqPrefix_preserves (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (r : ProductRxContracts I) (x : ProductWgXmitContracts I) :
    PrefixPreserves I LifetimeEvent.Safe napiSoftirqPrefix := by
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  unfold napiSoftirqPrefix
  apply PrefixEnsures.bind (getDev_saved_spec_product c (fun _ => True))
  intro d
  apply PrefixEnsures.bind (savedPeerFilterMap_spec_product c (fun _ => True) _ _)
  intro pending
  apply PrefixEnsures.consequence (show PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I) from ?_)
    (fun _ _ hi => hi.1) (fun _ _ _ hi => ⟨hi, True.intro⟩)
  change PrefixPreserves I LifetimeEvent.Safe _
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | with_reducible apply runWorkerPrefix_preserves c.safe c.storeStable
    | with_reducible exact rxPollStackPrefix_preserves c t r x _ _
    | with_reducible exact ProductAmbientContracts.drop (c.ambient (fun _ => True) AmbientM.peekHiddenSite)
    | exact ProductAmbientContracts.drop (c.ambient (fun _ => True) (get : AmbientM Ambient))
    | exact ProductAmbientContracts.drop (c.ambient (fun _ => True) (AmbientM.unsupported _))
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro z; try dsimp only)

  all_goals exact ProductAmbientContracts.drop (c.ambient (fun _ => True) AmbientM.peekHiddenSite)

/-- Scalar placement choice in the actual product environment component. -/
def chooseNapiHere : Leanux.M Bool := do
  let w ← getEnv
  let here := w.napiBeforePut.headD false
  modifyEnv fun e => {e with napiBeforePut := e.napiBeforePut.drop 1, napiAmbiguous := e.napiAmbiguous + 1}
  return here

def napiIrqExitPrefix : PrefixM LifetimeEvent Unit := do
  if (← liftPrefix getAmbient).hidden.isNone then return
  let d ← liftWGObserver (liftWGPrefix getDev)
  if !(← liftWGObserver (savedPeerAny (·.napiScheduled) d.peers.toList)) then return
  if (← liftPrefix peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  let here ← liftPrefix chooseNapiHere
  if here then napiSoftirqPrefix

def napiIrqExitSource : Leanux.M Unit := do
  if (← getAmbient).hidden.isNone then return
  if !(← getDev).peers.toList.any (·.2.napiScheduled) then return
  if (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  let here ← chooseNapiHere
  if here then Env.napiSoftirq

theorem napiIrqExitSource_eq : napiIrqExitSource = Env.napiIrqExit := by
  simp only [napiIrqExitSource, chooseNapiHere, Env.napiIrqExit, bind_assoc, pure_bind]

theorem napiIrqExitPrefix_erases : ErasesPrefix napiIrqExitPrefix Env.napiIrqExit := by
  rw [← napiIrqExitSource_eq]
  unfold napiIrqExitPrefix napiIrqExitSource
  repeat' first
    | with_reducible exact napiSoftirqPrefix_erases
    | with_reducible apply erasesPrefix_bind_pure (liftWGObserver_erases (savedPeerAny_erases _ _))
    | with_reducible exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

  all_goals exact liftWGObserver_erases (erasesStatePrefix_lift _)

theorem napiIrqExitPrefix_preserves (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (r : ProductRxContracts I) (x : ProductWgXmitContracts I) :
    PrefixPreserves I LifetimeEvent.Safe napiIrqExitPrefix := by
  unfold napiIrqExitPrefix
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.ambient (fun _ => True) (get : AmbientM Ambient)))
  intro world
  split
  · exact PrefixPreserves.pure c.safe _
  · apply ProductAmbientContracts.drop (Q := fun _ _ => True)
    apply PrefixEnsures.bind (getDev_saved_spec_product c (fun _ => True))
    intro d
    apply PrefixEnsures.bind (savedPeerAny_spec_product c (fun _ => True) _ _)
    intro pending
    apply PrefixEnsures.consequence (show PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I) from ?_)
      (fun _ _ hi => hi.1) (fun _ _ _ hi => ⟨hi, True.intro⟩)
    repeat' first
      | exact napiSoftirqPrefix_preserves c t r x
      | exact ProductAmbientContracts.drop (c.ambient (fun _ => True) AmbientM.peekHiddenSite)
      | exact ProductAmbientContracts.drop (c.store (fun _ => True) chooseNapiHere (by
          apply (ProjectedAction.iff_run _ _ _).mpr
          intro w x v hr
          cases hr
          rfl))
      | exact PrefixPreserves.pure c.safe _
      | apply PrefixPreserves.bind
      | split
      | (intro z; try dsimp only)

theorem napiSoftirqPrefix_allocation : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe napiSoftirqPrefix :=
  napiSoftirqPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient)
    (ProductTxContracts.ofNative allocationTx)
    ⟨fun len => (allocationRx.stats len).liftWGObserver,
      fun why => (allocationRx.dishonest why).liftWGObserver,
      fun id => (allocationRx.free id).liftWGObserver⟩
    ⟨fun P => (allocationWgXmit.errors P).liftWGObserver⟩

theorem napiIrqExitPrefix_allocation : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe napiIrqExitPrefix :=
  napiIrqExitPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient)
    (ProductTxContracts.ofNative allocationTx)
    ⟨fun len => (allocationRx.stats len).liftWGObserver,
      fun why => (allocationRx.dishonest why).liftWGObserver,
      fun id => (allocationRx.free id).liftWGObserver⟩
    ⟨fun P => (allocationWgXmit.errors P).liftWGObserver⟩

end Leanux.Proofs.WG.Lifetimes
