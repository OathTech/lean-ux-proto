import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialLifecycleFrames
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialTraffic
import Leanux.Proofs.WG.Packets.PublicationControls
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverDispatchFrames

/-! Environment lifecycle callbacks retain received allocation certificates, including
normal deletion, routing notifications and namespace cleanup. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem native_carrier {action : WG.M α} (native : Preserves (Bounded (h.filterMap Journal.origin?)) action) :
    Preserves (Carrier h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp native w a result v b hi.1 run,hi.2⟩

theorem product_carrier_lift (action : Leanux.M α)
    (native : ∀ h, Preserves (fun w : World => Carrier h w.wg) action) :
    ProductSafe (Leanux.Proofs.Logged.liftPrefix action) := by
  change Leanux.Proofs.Logged.PrefixEnsures (fun h (w : World) => Carrier h w.wg) Safe _
    (fun _ h (w : World) => Carrier h w.wg)
  apply Leanux.Proofs.Logged.PrefixEnsures.lift _ (fun _ _ hi => hi.2)
  intro h w result v hi run
  exact (hoare_iff_run _ _ _).mp (native h) w result v hi run

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution

namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution.Control
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransmitSecurity Responder
private theorem native (a : WG.M α) (h : List Journal.Event)
    (safe : Preserves (fun w => Carrier h w) a) :
    Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) :=
  PublicationPoll.native_product _ _ safe

private theorem product_store_frame (a : Leanux.M α) (frame : SameProductStore a) (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact product_stable h w v ((ProjectedAction.iff_run _ _ _).mp frame w x v hr) hi

private theorem effect (a : AmbientM α) (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) :=
  productAmbient_spec a _ (fun _ _ hi => hi)

private theorem route (a : Net.M α) (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) :=
  product_store_frame _ (fun s => productRouting_spec a (fun t => t = s)) h

private theorem readWG (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) (getWG : Leanux.M WGWorld) :=
  product_store_frame _ (fun s => productGetWG_spec (fun t => t = s)) h

private theorem readDev (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) (monadLift getDev : Leanux.M Device) :=
  native _ h (native_carrier (bounded_store getDev_sameWGStore))

private theorem editEnv (f : EnvWorld → EnvWorld) (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) (modifyEnv f) := by
  unfold modifyEnv
  apply hoare_modify
  exact fun _ hi => hi

private theorem idle (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) Env.requireIdleDevice :=
  product_store_frame _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store) h

theorem env_down (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) Env.wgDown := by
  have down := native _ h (native_carrier LifecycleFrames.down)
  have get := readWG h
  have stopped := idle h
  have effects {α : Type} (a : AmbientM α) := effect a h
  have routes {α : Type} (a : Net.M α) := route a h
  routing_tx_source [Env.wgDown,skipCut,modifyRouting] using [down,get,stopped,effects,routes]

theorem env_delete (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) Env.wgDelete := by
  have down := native _ h (native_carrier LifecycleFrames.down)
  have destruct := native _ h (native_carrier LifecycleFrames.destruct)
  have get := readWG h
  have dev := readDev h
  have stopped := idle h
  have slept := native _ h (native_carrier (bounded_store mayHaveSlept_sameWGStore))
  have inet := product_store_frame _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store) h
  have effects {α : Type} (a : AmbientM α) := effect a h
  have routes {α : Type} (a : Net.M α) := route a h
  routing_tx_source [Env.wgDelete,WG.wgDelete,skipCut,modifyRouting,unsupported]
    using [down,destruct,get,dev,stopped,slept,inet,effects,routes]

theorem env_cleanup (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) Env.netnsCleanup := by
  have preExit := native _ h (native_carrier LifecycleFrames.pre_exit)
  have effects {α : Type} (a : AmbientM α) := effect a h
  have routes {α : Type} (a : Net.M α) := route a h
  have env (f : EnvWorld → EnvWorld) := editEnv f h
  routing_tx_source [Env.netnsCleanup,Env.runWorker,Env.pendingDevice,getAmbient,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effects,routes,env]

theorem env_mtu (n : Nat) (h : List Journal.Event) :
    Preserves (fun w : World => Carrier h w.wg) (Env.setMtu n) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w x v run
  refine ⟨LifecycleFrames.transfer hi.1 ?_,hi.2⟩
  have fields := congrArg (fun s : ProductStore43 => LifecycleFrames.fields {dev:=s.2.2.2.dev}) same
  simpa only [LifecycleFrames.fields,envScalarView,envScalarStore,envScalarDevice,
    productStoreView,wgStoreView,Option.map_map,Function.comp_def] using fields

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution.Control
