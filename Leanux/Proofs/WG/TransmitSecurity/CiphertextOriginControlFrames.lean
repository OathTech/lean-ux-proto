import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginLifecycleFrames
import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginProductFrames
import Leanux.Proofs.WG.Packets.PublicationControls

/-! Environment lifecycle callbacks retain resident TX ciphertext certificates, including
normal deletion, routing notifications and namespace cleanup. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins.Control
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues
private theorem native (a : WG.M α) (h : List WorkerEncryption.Receipt)
    (safe : Preserves (fun w => Inv h w) a) :
    Preserves (fun w : World => Inv h w.wg) (monadLift a : Leanux.M α) :=
  PublicationPoll.native_product _ _ safe

private theorem product_store_frame (a : Leanux.M α) (frame : SameProductStore a) (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact product_store_inv h w v ((ProjectedAction.iff_run _ _ _).mp frame w x v hr) hi

private theorem effect (a : AmbientM α) (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) (monadLift a : Leanux.M α) :=
  productAmbient_spec a _ (fun _ _ hi => hi)

private theorem route (a : Net.M α) (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) (monadLift a : Leanux.M α) :=
  product_store_frame _ (fun s => productRouting_spec a (fun t => t = s)) h

private theorem readWG (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) (getWG : Leanux.M WGWorld) :=
  product_store_frame _ (fun s => productGetWG_spec (fun t => t = s)) h

private theorem readDev (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) (monadLift getDev : Leanux.M Device) :=
  native _ h (NativeFrames.store getDev_sameWGStore)

private theorem editEnv (f : EnvWorld → EnvWorld) (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) (modifyEnv f) := by
  unfold modifyEnv
  apply hoare_modify
  exact fun _ hi => hi

private theorem idle (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) Env.requireIdleDevice :=
  product_store_frame _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store) h

theorem env_down (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) Env.wgDown := by
  have down := native _ h (NativeFrames.down)
  have get := readWG h
  have stopped := idle h
  have effects {α : Type} (a : AmbientM α) := effect a h
  have routes {α : Type} (a : Net.M α) := route a h
  routing_tx_source [Env.wgDown,skipCut,modifyRouting] using [down,get,stopped,effects,routes]

theorem env_delete (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) Env.wgDelete := by
  have down := native _ h (NativeFrames.down)
  have destruct := native _ h (NativeFrames.destruct)
  have get := readWG h
  have dev := readDev h
  have stopped := idle h
  have slept := native _ h (NativeFrames.store mayHaveSlept_sameWGStore)
  have inet := product_store_frame _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store) h
  have effects {α : Type} (a : AmbientM α) := effect a h
  have routes {α : Type} (a : Net.M α) := route a h
  routing_tx_source [Env.wgDelete,WG.wgDelete,skipCut,modifyRouting,unsupported]
    using [down,destruct,get,dev,stopped,slept,inet,effects,routes]

theorem env_cleanup (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) Env.netnsCleanup := by
  have preExit := native _ h (NativeFrames.pre_exit)
  have effects {α : Type} (a : AmbientM α) := effect a h
  have routes {α : Type} (a : Net.M α) := route a h
  have env (f : EnvWorld → EnvWorld) := editEnv f h
  routing_tx_source [Env.netnsCleanup,Env.runWorker,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effects,routes,env]

theorem env_mtu (n : Nat) (h : List WorkerEncryption.Receipt) :
    Preserves (fun w : World => Inv h w.wg) (Env.setMtu n) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w x v hr
  apply hi.retains
  apply Retains.of_snapshot
  change (PacketOrigins.epoch v.wg,PacketPayload.view v.wg) = (PacketOrigins.epoch w.wg,PacketPayload.view w.wg)
  apply Prod.ext
  · have field := congrArg (fun s : ProductStore43 => s.2.2.2.dev.map (·.ifindex)) same
    simpa only [PacketOrigins.epoch,envScalarView,envScalarStore,envScalarDevice,
      productStoreView,wgStoreView,Option.map_map,Function.comp_def] using field
  · funext id
    have field := congrArg (fun s : ProductStore43 =>
      (s.2.2.2.dev.bind fun d => d.txSkbs[id]?).map PacketPayload.material) same
    simpa only [PacketPayload.view,TxDisposition.txPackets,envScalarView,envScalarStore,envScalarDevice,
      productStoreView,wgStoreView,Option.bind_map,Function.comp_def] using field

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins.Control
