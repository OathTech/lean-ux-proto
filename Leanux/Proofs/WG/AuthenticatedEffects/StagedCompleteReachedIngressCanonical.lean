import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIngressNativeFrames

/-! Literal receive-entry branches expose RX allocation, queue admission,
publication and counted peer release. Key-reference, header and CPU calls use atomic access trees; the remaining native
access atoms retain explicit separate interior obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Ingress
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver NestedPeerRelease

noncomputable def handshakeAppend (msg : Key) (src : SkbSource) : Shape (liftWGObserver (liftWGPrefix
    (modifyDev fun d=>{d with handshakeQueue:=d.handshakeQueue.produce (msg,src),handshakeQueueLen:=d.handshakeQueueLen+1}))) := by
  apply quietShape
  · complete_ingress_native
  · exact AllocatedFrames.observed (erasesStatePrefix_lift _) (allocationReceiveIngress.append msg src)

elab "ingress_source_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not an ingress shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  unless action.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
  let some source := action.getAppArgs.back? | Lean.throwError "missing WG source"
  let .const actual _ := source.consumeMData.headBeta.getAppFn | Lean.throwError "not a named source"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString==name || actual.toString.endsWith ("."++name) do Lean.throwError "different source head"

elab "ingress_native_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not an ingress shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
  let some source := action.getAppArgs.back? | Lean.throwError "missing observer"
  unless source.isAppOf ``liftWGPrefix do Lean.throwError "not a native atom"
  let some body := source.getAppArgs.back? | Lean.throwError "missing native body"
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a named native body"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString==name || actual.toString.endsWith ("."++name) do Lean.throwError "different native head"

macro "ingress_allocation_frame" : tactic => `(tactic| first
  | (rx_retention_head indexLookup; exact AllocatedFrames.observed (indexLookupPrefix_erases _ _)
      (indexLookupPrefix_preserves_ambient allocationAmbient _ _))
  | (rx_retention_head keypairGet; exact AllocatedFrames.observed (keypairGetPrefix_erases _) (keypairGetPrefix_allocation _))
  | (rx_retention_head keypairGetNull; exact AllocatedFrames.store keypairGetNull_sameStore)
  | (rx_retention_head keypairPut; exact AllocatedFrames.observed (keypairPutPrefix_erases _ _) (keypairPutPrefix_allocation _ _))
  | (rx_retention_head enqueuePerDeviceAndPeerRx; exact AllocatedFrames.observed
      (enqueuePerDeviceAndPeerRxPrefix_erases _) (enqueuePerDeviceAndPeerRxPrefix_allocation _))
  | (rx_retention_head RxWorkers.publishSource; exact AllocatedFrames.observed (RxWorkers.publish_erases _ _) (RxWorkers.publish_preserves _ _))
  | (rx_retention_head prepareSkbHeader; exact AllocatedFrames.store ((prepareSkbHeader_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head ipTunnelGetDsfield; exact AllocatedFrames.store ((ipTunnelGetDsfield_sameWGWorld _ _).factor wgStoreView))
  | (rx_retention_head cpumaskNextOnline; exact AllocatedFrames.observed cpumaskNextOnlinePrefix_erases
      (cpumaskNextOnlinePrefix_preserves allocationAmbient allocationReceiveIngress))
  | (rx_retention_head queueDeviceWork; unfold queueDeviceWork; exact hoare_liftAmbient _ _)
  | entry_device_allocation)

macro "ingress_source_step" : tactic => `(tactic| first
  | dsimp +failIfUnchanged only
  | (ingress_native_head newRxSkb; exact .native (.allocate _))
  | (ingress_native_head freeRxSkb; exact .native (.free _))
  | (ingress_native_head modifyDev; exact handshakeAppend _ _)
  | (ingress_source_head Hooks.peerRelease; exact .release _)
  | (ingress_native_head enqueuePerDeviceAndPeerRx; exact .native (.rxQueue _))
  | (ingress_native_head indexLookup; exact .native (.lookup _ _))
  | (ingress_native_head keypairGet; apply accessShape _ (Access.getShape _); solve | ingress_allocation_frame)
  | (ingress_native_head keypairGetNull; apply accessShape _ Access.nullShape; solve | ingress_allocation_frame)
  | (ingress_native_head keypairPut; apply accessShape _ (Access.putShape _ _); solve | ingress_allocation_frame)
  | (ingress_native_head prepareSkbHeader; apply accessShape _ (Access.headerShape _); solve | ingress_allocation_frame)
  | (ingress_native_head ipTunnelGetDsfield; apply accessShape _ (Access.dsfieldShape _ _); solve | ingress_allocation_frame)
  | (ingress_native_head cpumaskNextOnline; apply accessShape _ Access.cpuShape; solve | ingress_allocation_frame)
  | (ingress_source_head liftWGPrefix
     apply quietShape
     · solve | complete_ingress_native
     · solve | ingress_allocation_frame)
  | (ingress_source_head Pure.pure; exact pureShape _)
  | (ingress_source_head Bind.bind; apply observerBindShape)
  | (ingress_source_head ite; apply conditionalShape)
  | intro value
  | split)

noncomputable def publication (skb : SkbId) : Shape (liftWGObserver (publishWith (nestedOps hooks) (pure ()) skb .dead)) := by
  unfold publishWith
  simp only [nestedOps]
  repeat' ingress_source_step

noncomputable def admission (msg : Key) (src : SkbSource) (ds : Nat) :
    Shape (liftWGObserver (admitWith (nestedOps hooks) (fun packet=>liftWGPrefix (newRxSkb packet)) msg src ds)) := by
  unfold admitWith RxOrigin.admitWith
  simp only [nestedOps,monadLift_self]
  repeat' ingress_source_step

noncomputable def finish (entry : RxOrigin.Admission) : Shape (liftWGObserver
    (ingressFinishWith (nestedOps hooks) (fun skb=>publishWith (nestedOps hooks) (pure ()) skb .dead) entry)) := by
  unfold ingressFinishWith RxOrigin.finishWith
  simp only [nestedOps,monadLift_self]
  repeat' first
    | (ingress_source_head publishWith; exact publication _)
    | ingress_source_step

noncomputable def data (msg : Key) (src : SkbSource) (ds : Nat) :
    Shape (liftWGObserver (ingress (nestedOps hooks) msg src ds)) := by
  unfold ingress ingressWith
  repeat' first
    | (ingress_source_head admitWith; exact admission _ _ _)
    | (ingress_source_head ingressFinishWith; exact finish _)
    | ingress_source_step

noncomputable def canonical (msg : Key) (src : SkbSource) : Shape (receiveEntryObserved hooks msg src) := by
  unfold receiveEntryObserved receive receiveWith packetReceiveWith
  simp only [nestedOps]
  repeat' first
    | (ingress_source_head ingress; exact data _ _ _)
    | ingress_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Ingress
