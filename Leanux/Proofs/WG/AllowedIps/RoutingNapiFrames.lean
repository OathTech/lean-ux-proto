import Leanux.Proofs.WG.AllowedIps.RoutingRxFrames
import Leanux.Proofs.Framing.Batch
import Leanux.Proofs.WG.Lifetimes.BatchNapi

/-! Concrete NET_RX and crypt-worker callbacks. The original captured pending
list, ambiguity choice, records and unsupported cases remain intact. These
normal-endpoint frames permit deletion and require no resident-list premise. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem runWorker_routing (worker : Worker) (body : Leanux.M Unit)
    (hb : ProductRetainsRoutingCall body) : ProductRetainsRoutingCall (Env.runWorker worker body) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have device : Preserves P (monadLift getDev : Leanux.M Device) :=
    productGetDev_spec (fun store => Q (store.2.2.2.dev.map routingState))
  have bodyFrame : Preserves P body := RetainsRoutingCall.wp hb s
  have main : Preserves P (Env.runWorker worker body) := by
    routing_tx_source [Env.runWorker, hidden, modifyAmbient] using [bodyFrame, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

private theorem pendingPolls_routing (pending : List PeerId) :
    ProductRetainsRoutingCall (do
      for pid in pending do
        discard <| rxPoll pid NAPI_POLL_WEIGHT (fun xs => xs.forM Env.deliverInner)) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have device : Preserves P (monadLift getDev : Leanux.M Device) :=
    productGetDev_spec (fun store => Q (store.2.2.2.dev.map routingState))
  have poll (pid : PeerId) : Preserves P (rxPoll pid NAPI_POLL_WEIGHT (fun xs => xs.forM Env.deliverInner)) :=
    RetainsRoutingCall.wp (actualRxPoll_routing pid NAPI_POLL_WEIGHT) s
  have main : Preserves P (do
      for pid in pending do
        discard <| rxPoll pid NAPI_POLL_WEIGHT (fun xs => xs.forM Env.deliverInner)) := by
    routing_tx_source [] using [poll]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem napiSoftirq_routing : ProductRetainsRoutingCall Env.napiSoftirq := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have device : Preserves P (monadLift getDev : Leanux.M Device) :=
    productGetDev_spec (fun store => Q (store.2.2.2.dev.map routingState))
  have worker (pending : List PeerId) : Preserves P (Env.runWorker .netRx (do
      for pid in pending do
        discard <| rxPoll pid NAPI_POLL_WEIGHT (fun xs => xs.forM Env.deliverInner))) :=
    RetainsRoutingCall.wp (runWorker_routing .netRx _ (pendingPolls_routing pending)) s
  have main : Preserves P Env.napiSoftirq := by
    routing_tx_source [Env.napiSoftirq, getAmbient, peekHiddenSite] using [worker, device, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

/-- The second actual direct poll site runs without opening a new section. -/
theorem pollScheduledInline_routing : ProductRetainsRoutingCall Env.pollScheduledInline := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have device : Preserves P (monadLift getDev : Leanux.M Device) :=
    productGetDev_spec (fun store => Q (store.2.2.2.dev.map routingState))
  have poll (pid : PeerId) : Preserves P (rxPoll pid NAPI_POLL_WEIGHT (fun xs => xs.forM Env.deliverInner)) :=
    RetainsRoutingCall.wp (actualRxPoll_routing pid NAPI_POLL_WEIGHT) s
  have main : Preserves P Env.pollScheduledInline := by
    routing_tx_source [Env.pollScheduledInline] using [poll, device, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem napiIrqExit_routing : ProductRetainsRoutingCall Env.napiIrqExit := by
  rw [← napiIrqExitSource_eq]
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have device : Preserves P (monadLift getDev : Leanux.M Device) :=
    productGetDev_spec (fun store => Q (store.2.2.2.dev.map routingState))
  have softirq : Preserves P Env.napiSoftirq := RetainsRoutingCall.wp napiSoftirq_routing s
  have choice : Preserves P chooseNapiHere := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  have main : Preserves P napiIrqExitSource := by
    routing_tx_source [napiIrqExitSource, getAmbient, peekHiddenSite] using [choice, softirq, device, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem actualEncryptStep_routing : ProductRetainsRoutingCall (encryptStep Env.checksumHelp Env.napiSoftirq) :=
  encryptStep_routing _ _ actualChecksum_routing napiSoftirq_routing

theorem actualEncryptIter_routing :
    ProductRetainsRoutingCall (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
  encryptIter_routing _ _ _ actualChecksum_routing napiSoftirq_routing
    (ProjectedRetainsRoutingCall.of_same
      ((Framing.condResched_sameKernel .encryptWorker).of_factor
        (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
        (fun w : World => routingView w.wg) (fun _ => rfl)))

theorem actualDecryptStep_routing : ProductRetainsRoutingCall (decryptStep Env.napiSoftirq Env.napiIrqExit) :=
  decryptStep_routing _ _ napiSoftirq_routing napiIrqExit_routing

theorem actualDecryptIter_routing :
    ProductRetainsRoutingCall (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
  decryptIter_routing _ _ _ napiSoftirq_routing napiIrqExit_routing
    (ProjectedRetainsRoutingCall.of_same
      ((Framing.condResched_sameKernel .decryptWorker).of_factor
        (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
        (fun w : World => routingView w.wg) (fun _ => rfl)))

theorem actualTxIter_routing (pid : PeerId) : ProductRetainsRoutingCall (txIter pid (Env.condResched .txWorker)) :=
  txIter_routing _ _ (ProjectedRetainsRoutingCall.of_same
      ((Framing.condResched_sameKernel .txWorker).of_factor
        (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
        (fun w : World => routingView w.wg) (fun _ => rfl)))

end Leanux.Proofs.WG.AllowedIps
