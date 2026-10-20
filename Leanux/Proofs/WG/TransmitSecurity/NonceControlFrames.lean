import Leanux.Proofs.WG.TransmitSecurity.NonceDeviceFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceTraffic
import Leanux.Proofs.WG.Packets.PublicationControls

/-! Native environment lifecycle controls transport the nonce projection.
Their route, descriptor, clock and namespace bookkeeping cannot reset keys. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

private theorem native (a : WG.M α) (h : List Allocation)
    (safe : Preserves (fun w => Inv (view w) h) a) :
    Preserves (fun w : World => Inv (view w.wg) h) (monadLift a : Leanux.M α) :=
  PublicationPoll.native_product _ _ safe

private theorem product_store_frame (a : Leanux.M α) (frame : SameProductStore a) (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact product_store h w v ((ProjectedAction.iff_run _ _ _).mp frame w x v hr) hi

private theorem effect (a : AmbientM α) (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) (monadLift a : Leanux.M α) :=
  productAmbient_spec a _ (fun _ _ hi => hi)

private theorem route (a : Net.M α) (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) (monadLift a : Leanux.M α) :=
  product_store_frame _ (fun s => productRouting_spec a (fun t => t = s)) h

private theorem readWG (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) (getWG : Leanux.M WGWorld) :=
  product_store_frame _ (fun s => productGetWG_spec (fun t => t = s)) h

private theorem readDev (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) (monadLift getDev : Leanux.M Device) :=
  native _ h (native_frame h device_read)

private theorem editEnv (f : EnvWorld → EnvWorld) (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) (modifyEnv f) := by
  unfold modifyEnv
  apply hoare_modify
  exact fun _ hi => hi

private theorem idle (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) Env.requireIdleDevice :=
  product_store_frame _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store) h

theorem env_down (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) Env.wgDown := by
  have down := native _ h (down_device h)
  have get := readWG h
  have stopped := idle h
  have effects {α : Type} (a : AmbientM α) := effect a h
  have routes {α : Type} (a : Net.M α) := route a h
  routing_tx_source [Env.wgDown,skipCut,modifyRouting] using [down,get,stopped,effects,routes]

theorem env_delete (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) Env.wgDelete := by
  have down := native _ h (down_device h)
  have destruct := native _ h (destruct_device h)
  have get := readWG h
  have dev := readDev h
  have stopped := idle h
  have slept := native _ h (native_frame h (store mayHaveSlept_sameWGStore))
  have inet := product_store_frame _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store) h
  have effects {α : Type} (a : AmbientM α) := effect a h
  have routes {α : Type} (a : Net.M α) := route a h
  routing_tx_source [Env.wgDelete,WG.wgDelete,skipCut,modifyRouting,unsupported]
    using [down,destruct,get,dev,stopped,slept,inet,effects,routes]

theorem pre_exit : SameView view netnsPreExit :=
  full Origins.Retaining.netnsPreExit_material Keypairs.WGDevice.netnsPreExit_sameSnapshot

theorem env_cleanup (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) Env.netnsCleanup := by
  have preExit := native _ h (native_frame h pre_exit)
  have effects {α : Type} (a : AmbientM α) := effect a h
  have routes {α : Type} (a : Net.M α) := route a h
  have env (f : EnvWorld → EnvWorld) := editEnv f h
  have pending := product_store_frame _ (pendingDevice_sameKernel .netnsCleanup false) h
  routing_tx_source [Env.netnsCleanup,Env.runWorker,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effects,routes,env,pending]

theorem env_mtu (n : Nat) (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) (Env.setMtu n) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w x v hr
  have field := congrArg (fun s : ProductStore43 => nonceStore s.2.2.2) same
  have eq : view v.wg = view w.wg := by
    simpa [nonceStore,view,envScalarView,envScalarStore,envScalarDevice,productStoreView,
      wgStoreView,Option.bind_map,Function.comp_def] using field
  simpa only [eq] using hi

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
