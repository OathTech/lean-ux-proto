import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionLifecycleFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion.Environment
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
  have counter : v.wg.keypairCounter = w.wg.keypairCounter := congrArg (fun s : ProductStore43 => s.2.2.2.keypairCounter) same
  refine ⟨?_,CurrentSlots.fields_transport hi.2.1 ?_,hi.2.2.retained ?_⟩
  · intro s hs
    apply hi.1 s
    simpa only [ConfiguredIdentity.view,device] using hs
  · unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]
  · have projection : view v.wg = view w.wg := by
      have keys : keypairResidents v.wg = keypairResidents w.wg := by
        funext kid; simp only [keypairResidents,device]
      simp only [view,nextSlot,keys,device,counter]
    rw [projection]
    exact Retained.refl _

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
      (monadLift getDev : Leanux.M Device) := native _ confirmed (Carrier.store confirmed getDev_sameWGStore)

private theorem modifyEnv_spec (f : EnvWorld → EnvWorld) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) (modifyEnv f) := by
  unfold modifyEnv
  apply hoare_modify
  exact fun _ hi => hi

private theorem idle (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) Env.requireIdleDevice :=
  store _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store) confirmed

theorem down (frames : H1LifecycleFrames) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) Env.wgDown := by
  have down := native _ confirmed (Carrier.down frames confirmed)
  have get := readWG confirmed
  have stopped := idle confirmed
  have effect {α : Type} (a : AmbientM α) := native_ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  routing_tx_source [Env.wgDown,skipCut,modifyRouting] using [down,get,stopped,effect,route]

theorem delete (frames : H1LifecycleFrames) (config : H1ConfigurationFrames) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) Env.wgDelete := by
  have down := native _ confirmed (Carrier.down frames confirmed)
  have destruct := native _ confirmed (Carrier.destruct config confirmed)
  have get := readWG confirmed
  have dev := readDev confirmed
  have stopped := idle confirmed
  have slept := native _ confirmed (Carrier.store confirmed mayHaveSlept_sameWGStore)
  have inet := store _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store) confirmed
  have effect {α : Type} (a : AmbientM α) := native_ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  routing_tx_source [Env.wgDelete,WG.wgDelete,skipCut,modifyRouting,unsupported]
    using [down,destruct,get,dev,stopped,slept,inet,effect,route]

theorem cleanup (config : H1ConfigurationFrames) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) Env.netnsCleanup := by
  have preExit := native _ confirmed (Carrier.pre_exit config confirmed)
  have effect {α : Type} (a : AmbientM α) := native_ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  have env (f : EnvWorld → EnvWorld) := modifyEnv_spec f confirmed
  routing_tx_source [Env.netnsCleanup,Env.runWorker,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effect,route,env]

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion.Environment
