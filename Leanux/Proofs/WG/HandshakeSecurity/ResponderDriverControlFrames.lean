import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverLifecycleFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

private theorem native (a : WG.M α) (confirmed : List Nat)
    (ha : Framing.Preserves (Carrier confirmed) a) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg)
      (monadLift a : Leanux.M α) := PublicationPoll.native_product _ _ ha

private theorem store (a : Leanux.M α) (frame : SameProductStore a) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  have same := (ProjectedAction.iff_run _ _ _).mp frame w x v run
  have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  refine ⟨?_,(hoare_iff_run _ _ _).mp (native_product_store frame confirmed) w x v hi.2 run⟩
  intro s hs
  apply hi.1 s
  simpa only [ConfiguredIdentity.view,device] using hs

private theorem native_ambient (a : AmbientM α) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg)
      (monadLift a : Leanux.M α) := productAmbient_spec a _ (fun _ _ hi => hi)

private theorem routing (a : Net.M α) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg)
      (monadLift a : Leanux.M α) :=
  store _ (fun s => productRouting_spec a (fun t => t = s)) confirmed

private theorem readWG (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) (getWG : Leanux.M WGWorld) :=
  store _ (fun s => productGetWG_spec (fun t => t = s)) confirmed

private theorem readDev (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg)
      (monadLift getDev : Leanux.M Device) := native _ confirmed (carrier_store getDev_sameWGStore confirmed)

private theorem modifyEnv_spec (f : EnvWorld → EnvWorld) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) (modifyEnv f) := by
  unfold modifyEnv
  apply hoare_modify
  exact fun _ hi => hi

private theorem idle (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) Env.requireIdleDevice :=
  store _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store) confirmed

theorem carrier_env_down (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) Env.wgDown := by
  have down := native _ confirmed (carrier_down H1 confirmed)
  have get := readWG confirmed
  have stopped := idle confirmed
  have effect {α : Type} (a : AmbientM α) := native_ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  routing_tx_source [Env.wgDown,skipCut,modifyRouting] using [down,get,stopped,effect,route]

theorem carrier_env_delete (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) Env.wgDelete := by
  have down := native _ confirmed (carrier_down H1 confirmed)
  have destruct := native _ confirmed (carrier_destruct H1 confirmed)
  have get := readWG confirmed
  have dev := readDev confirmed
  have stopped := idle confirmed
  have slept := native _ confirmed (carrier_store mayHaveSlept_sameWGStore confirmed)
  have inet := store _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store) confirmed
  have effect {α : Type} (a : AmbientM α) := native_ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  routing_tx_source [Env.wgDelete,WG.wgDelete,skipCut,modifyRouting,unsupported]
    using [down,destruct,get,dev,stopped,slept,inet,effect,route]

theorem carrier_env_cleanup (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) Env.netnsCleanup := by
  have preExit := native _ confirmed (carrier_pre_exit confirmed)
  have effect {α : Type} (a : AmbientM α) := native_ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  have env (f : EnvWorld → EnvWorld) := modifyEnv_spec f confirmed
  routing_tx_source [Env.netnsCleanup,Env.runWorker,Env.pendingDevice,getAmbient,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effect,route,env]

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
