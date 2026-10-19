import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveLifecycle

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

private theorem native (a : WG.M α) (confirmed : List TimestampReceipt)
    (ha : Framing.Preserves (StateInv confirmed) a) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg)
      (monadLift a : Leanux.M α) := PublicationPoll.native_product _ _ ha

private theorem store (a : Leanux.M α) (frame : SameProductStore a) (confirmed : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  have same := (ProjectedAction.iff_run _ _ _).mp frame w x v run
  exact product_stable confirmed w v same hi

private theorem native_ambient (a : AmbientM α) (confirmed : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg)
      (monadLift a : Leanux.M α) := productAmbient_spec a _ (fun _ _ hi => hi)

private theorem routing (a : Net.M α) (confirmed : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg)
      (monadLift a : Leanux.M α) :=
  store _ (fun s => productRouting_spec a (fun t => t = s)) confirmed

private theorem readWG (confirmed : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg) (getWG : Leanux.M WGWorld) :=
  store _ (fun s => productGetWG_spec (fun t => t = s)) confirmed

private theorem readDev (confirmed : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg)
      (monadLift getDev : Leanux.M Device) := native _ confirmed (frame_store confirmed _ getDev_sameWGStore)

private theorem modifyEnv_spec (f : EnvWorld → EnvWorld) (confirmed : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg) (modifyEnv f) := by
  unfold modifyEnv
  apply hoare_modify
  exact fun _ hi => hi

private theorem idle (confirmed : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg) Env.requireIdleDevice :=
  store _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store) confirmed

theorem env_down (confirmed : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg) Env.wgDown := by
  have down := native _ confirmed (down confirmed)
  have get := readWG confirmed
  have stopped := idle confirmed
  have effect {α : Type} (a : AmbientM α) := native_ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  routing_tx_source [Env.wgDown,skipCut,modifyRouting] using [down,get,stopped,effect,route]

theorem env_delete (confirmed : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg) Env.wgDelete := by
  have down := native _ confirmed (down confirmed)
  have destruct := native _ confirmed (destruct confirmed)
  have get := readWG confirmed
  have dev := readDev confirmed
  have stopped := idle confirmed
  have slept := native _ confirmed (frame_store confirmed _ mayHaveSlept_sameWGStore)
  have inet := store _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store) confirmed
  have effect {α : Type} (a : AmbientM α) := native_ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  routing_tx_source [Env.wgDelete,WG.wgDelete,skipCut,modifyRouting,unsupported]
    using [down,destruct,get,dev,stopped,slept,inet,effect,route]

theorem env_cleanup (confirmed : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv confirmed w.wg) Env.netnsCleanup := by
  have preExit := native _ confirmed (pre_exit confirmed)
  have effect {α : Type} (a : AmbientM α) := native_ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  have env (f : EnvWorld → EnvWorld) := modifyEnv_spec f confirmed
  routing_tx_source [Env.netnsCleanup,Env.runWorker,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effect,route,env]

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
