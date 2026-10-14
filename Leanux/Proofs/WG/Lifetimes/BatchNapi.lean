import Leanux.Proofs.WG.Lifetimes.StackAccess
import Leanux.Proofs.WG.Lifetimes.SavedPeers
import Leanux.Proofs.Logged.PrefixBatch

/-! Exact NET_RX dispatch observations. Captured peer-map predicates are
observed before any poll callback can change the resident store. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def napiSoftirqPrefix : MixedM Unit := do
  let d ← liftPrefix getDev
  let pending ← savedPeerFilterMap (fun pid p => if p.napiScheduled then some pid else none) d.peers.toList
  if pending.isEmpty then return
  if (← liftPrefix get).hidden.isSome && (← liftPrefix peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  if pending.length > 1 then liftPrefix (unsupported "NAPI polls of several peers in one softirq")
  runWorkerPrefix .netRx do
    for pid in pending do
      discard <| rxPollStackPrefix pid NAPI_POLL_WEIGHT

theorem napiSoftirqPrefix_erases : ErasesPrefix napiSoftirqPrefix Env.napiSoftirq := by
  unfold napiSoftirqPrefix Env.napiSoftirq
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro d
  have h := savedPeerFilterMap_erases (fun pid p => if p.napiScheduled then some pid else none) d.peers.toList
  apply erasesPrefix_bind_pure h
  dsimp only
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible exact rxPollStackPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem napiSoftirqPrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (r : RxContracts I) (x : WgXmitContracts I) :
    PrefixPreserves I LifetimeEvent.Safe napiSoftirqPrefix := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  unfold napiSoftirqPrefix
  apply PrefixEnsures.bind (getDev_saved_spec c (fun _ => True))
  intro d
  apply PrefixEnsures.bind (savedPeerFilterMap_spec c (fun _ => True) _ _)
  intro pending
  apply PrefixEnsures.consequence (show PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I) from ?_)
    (fun _ _ hi => hi.1) (fun _ _ _ hi => ⟨hi, True.intro⟩)
  change PrefixPreserves I LifetimeEvent.Safe _
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | with_reducible apply runWorkerPrefix_preserves c.safe c.kernelStable
    | with_reducible exact rxPollStackPrefix_preserves c t r x _ _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ peekHiddenSite_sameKernel)
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w x v hr; cases hr; rfl))
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w x v hr; cases hr))
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro z; try dsimp only)

/-- Scalar placement choice only: the original get/set are retained together. -/
def chooseNapiHere : M Bool := do
  let w ← get
  let here := w.napiBeforePut.headD false
  set {w with napiBeforePut := w.napiBeforePut.drop 1, napiAmbiguous := w.napiAmbiguous + 1}
  return here

theorem chooseNapiHere_sameKernel : SameKernel chooseNapiHere := by
  intro w x v hr
  cases hr
  rfl

def napiIrqExitPrefix : MixedM Unit := do
  if (← liftPrefix get).hidden.isNone then return
  let d ← liftPrefix getDev
  if !(← savedPeerAny (·.napiScheduled) d.peers.toList) then return
  if (← liftPrefix peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  let here ← liftPrefix chooseNapiHere
  if here then napiSoftirqPrefix

def napiIrqExitSource : M Unit := do
  if (← get).hidden.isNone then return
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
    | with_reducible apply erasesPrefix_bind_pure (savedPeerAny_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem napiIrqExitPrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (r : RxContracts I) (x : WgXmitContracts I) :
    PrefixPreserves I LifetimeEvent.Safe napiIrqExitPrefix := by
  unfold napiIrqExitPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w x v hr; cases hr; rfl)))
  intro world
  split
  · exact PrefixPreserves.pure c.safe _
  · apply AmbientContracts.drop (Q := fun _ _ => True)
    apply PrefixEnsures.bind (getDev_saved_spec c (fun _ => True))
    intro d
    apply PrefixEnsures.bind (savedPeerAny_spec c (fun _ => True) _ _)
    intro pending
    apply PrefixEnsures.consequence (show PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I) from ?_)
      (fun _ _ hi => hi.1) (fun _ _ _ hi => ⟨hi, True.intro⟩)
    repeat' first
      | exact napiSoftirqPrefix_preserves c t r x
      | exact AmbientContracts.drop (c.kernel (fun _ => True) _ peekHiddenSite_sameKernel)
      | exact AmbientContracts.drop (c.kernel (fun _ => True) _ chooseNapiHere_sameKernel)
      | exact PrefixPreserves.pure c.safe _
      | apply PrefixPreserves.bind
      | split
      | (intro z; try dsimp only)

theorem napiSoftirqPrefix_allocation : PrefixPreserves AllocationInv LifetimeEvent.Safe napiSoftirqPrefix :=
  napiSoftirqPrefix_preserves allocationAmbient allocationTx allocationRx allocationWgXmit

theorem napiIrqExitPrefix_allocation : PrefixPreserves AllocationInv LifetimeEvent.Safe napiIrqExitPrefix :=
  napiIrqExitPrefix_preserves allocationAmbient allocationTx allocationRx allocationWgXmit

end Leanux.Proofs.WG.Lifetimes
