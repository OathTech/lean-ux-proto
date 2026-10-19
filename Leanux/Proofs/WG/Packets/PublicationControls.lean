import Leanux.Proofs.WG.Packets.PublicationDeviceConfiguration
import Leanux.Proofs.WG.Packets.PublicationAudited
import Leanux.Proofs.WG.Origins.OwnerControlCalls

/-! Exact environment device controls retain packet certificates. The routing,
ambient and fixture effects keep their actual subsystem domains, and the
existing audit observers retain their reached prefixes. -/
namespace Leanux.Proofs.WG.PublicationControls
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

private theorem native (a : WG.M α) (history : List RxHistory.Event)
    (ha : Framing.Preserves (PublicationFrontier.Inv history) a) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (monadLift a : Leanux.M α) := PublicationPoll.native_product _ _ ha

private theorem store (a : Leanux.M α) (frame : SameProductStore a)
    (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) a :=
  (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationFrontierPoll.«0».Leanux.Proofs.WG.PublicationFrontier.product_store) a frame history

private theorem ambient (a : AmbientM α) (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (monadLift a : Leanux.M α) := productAmbient_spec a _ (fun _ _ hi => hi)

private theorem routing (a : Net.M α) (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (monadLift a : Leanux.M α) :=
  store _ (fun s => productRouting_spec a (fun t => t = s)) history

private theorem readWG (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) (getWG : Leanux.M WGWorld) :=
  store _ (fun s => productGetWG_spec (fun t => t = s)) history

private theorem readDev (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (monadLift getDev : Leanux.M Device) := native _ history (PublicationFrontier.store_preserves getDev_sameWGStore history)

private theorem modifyEnv_spec (f : EnvWorld → EnvWorld) (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) (modifyEnv f) := by
  unfold modifyEnv
  apply hoare_modify
  exact fun _ hi => hi

private theorem idle (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) Env.requireIdleDevice :=
  store _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store) history

private theorem up_source (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) Env.wgUp := by
  have up := native _ history (PublicationFrontier.wgUp_preserves history)
  have get := readWG history
  have effect {α : Type} (a : AmbientM α) := ambient a history
  have route {α : Type} (a : Net.M α) := routing a history
  have env (f : EnvWorld → EnvWorld) := modifyEnv_spec f history
  routing_tx_source [Env.wgUp,skipCut] using [up,get,effect,route,env]

private theorem down_source (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) Env.wgDown := by
  have down := native _ history (PublicationFrontier.wgDown_preserves history)
  have get := readWG history
  have stopped := idle history
  have effect {α : Type} (a : AmbientM α) := ambient a history
  have route {α : Type} (a : Net.M α) := routing a history
  routing_tx_source [Env.wgDown,skipCut,modifyRouting] using [down,get,stopped,effect,route]

private theorem delete_source (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) Env.wgDelete := by
  have down := native _ history (PublicationFrontier.wgDown_preserves history)
  have destruct := native _ history (PublicationFrontier.wgDestruct_preserves history)
  have get := readWG history
  have dev := readDev history
  have stopped := idle history
  have slept := native _ history (PublicationFrontier.store_preserves mayHaveSlept_sameWGStore history)
  have inet := store _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store) history
  have effect {α : Type} (a : AmbientM α) := ambient a history
  have route {α : Type} (a : Net.M α) := routing a history
  routing_tx_source [Env.wgDelete,WG.wgDelete,skipCut,modifyRouting,unsupported]
    using [down,destruct,get,dev,stopped,slept,inet,effect,route]

private theorem cleanup_source (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) Env.netnsCleanup := by
  have preExit := native _ history (PublicationFrontier.netnsPreExit_preserves history)
  have effect {α : Type} (a : AmbientM α) := ambient a history
  have route {α : Type} (a : Net.M α) := routing a history
  have env (f : EnvWorld → EnvWorld) := modifyEnv_spec f history
  routing_tx_source [Env.netnsCleanup,Env.runWorker,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effect,route,env]

theorem up : PublicationJoint.Preserves (RxHistory.audit envWgUpAudit) :=
  PublicationJoint.combine _ OwnerControlCalls.up (PublicationAudited.source _ _ envWgUpAudit_erases up_source)

theorem down : PublicationJoint.Preserves (RxHistory.audit envWgDownAudit) :=
  PublicationJoint.combine _ OwnerControlCalls.down (PublicationAudited.source _ _ envWgDownAudit_erases down_source)

theorem delete : PublicationJoint.Preserves (RxHistory.audit envWgDeleteAudit) :=
  PublicationJoint.combine _ OwnerControlCalls.delete (PublicationAudited.source _ _ envWgDeleteAudit_erases delete_source)

theorem netnsCleanup : PublicationJoint.Preserves (RxHistory.audit envNetnsCleanupAudit) :=
  PublicationJoint.combine _ OwnerControlCalls.netnsCleanup
    (PublicationAudited.source _ _ envNetnsCleanupAudit_erases cleanup_source)

private theorem scalar (history : List RxHistory.Event) (w v : World)
    (same : envScalarView v = envScalarView w)
    (hi : PublicationFrontier.Inv history w.wg) : PublicationFrontier.Inv history v.wg := by
  have packets : RxDisposition.nativeRxStore v.wg = RxDisposition.nativeRxStore w.wg := by
    have fields := congrArg (fun s : ProductStore43 =>
      (s.2.2.2.dev.map (·.ifindex),fun (id : SkbId) => s.2.2.2.dev.bind fun d => d.rxSkbs[id]?)) same
    simpa only [RxDisposition.nativeRxStore,envScalarView,envScalarStore,productStoreView,
      envScalarDevice,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def] using fields
  have front : PublicationFrontier.frontier v.wg = PublicationFrontier.frontier w.wg := by
    have fields := congrArg (fun s : ProductStore43 => s.2.2.2.dev.map fun d => (d.ifindex,d.nextPeer)) same
    simpa only [PublicationFrontier.frontier,envScalarView,envScalarStore,productStoreView,
      envScalarDevice,wgStoreView,Option.map_map,Function.comp_def] using fields
  have peers : CurrentIdentity.peerView v.wg = CurrentIdentity.peerView w.wg := by
    have fields := congrArg (fun s : ProductStore43 => CurrentIdentity.peerView {dev := s.2.2.2.dev}) same
    simpa only [CurrentIdentity.peerView,envScalarView,envScalarStore,productStoreView,
      envScalarDevice,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def] using fields
  apply hi.transport_cells
  · intro id pkt cell _
    exact ⟨packets ▸ cell,
      congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst packets)⟩
  · exact PublicationFrontier.FrontiersLe.of_eq front
  · apply PublicationCompletion.peers_fields
    intro pid ident current
    simpa only [peers] using current

theorem mtu (n : Nat) : PublicationJoint.Preserves (RxHistory.audit (setMtuAudit n)) := by
  apply PublicationJoint.combine _ (OwnerControlCalls.mtu n)
  apply PublicationAudited.source _ _ (setMtuAudit_erases n)
  intro history
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact scalar history w v ((ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w x v hr) hi

theorem create : PublicationJoint.Preserves (RxHistory.mixed (liftWGObserver wgCreatePrefix)) :=
  PublicationJoint.native_mixed _ _ OwnerControlCalls.create wgCreatePrefix_erases
    PublicationFrontier.wgCreate_preserves

end Leanux.Proofs.WG.PublicationControls
