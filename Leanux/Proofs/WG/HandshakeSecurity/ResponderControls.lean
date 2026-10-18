import Leanux.Proofs.WG.HandshakeSecurity.ResponderDump

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Controls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

private theorem native (a : WG.M α) (confirmed : List Nat)
    (ha : Framing.Preserves (History.Native confirmed) a) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg)
      (monadLift a : Leanux.M α) := PublicationPoll.native_product _ _ ha

private theorem store (a : Leanux.M α) (frame : SameProductStore a) (confirmed : List Nat) :
    Framing.Preserves (AuditedFrames.State confirmed) a := native_product_store frame confirmed

private theorem ambient (a : AmbientM α) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg)
      (monadLift a : Leanux.M α) := productAmbient_spec a _ (fun _ _ hi => hi)

private theorem routing (a : Net.M α) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg)
      (monadLift a : Leanux.M α) :=
  store _ (fun s => productRouting_spec a (fun t => t = s)) confirmed

private theorem readWG (confirmed : List Nat) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg) (getWG : Leanux.M WGWorld) :=
  store _ (fun s => productGetWG_spec (fun t => t = s)) confirmed

private theorem readDev (confirmed : List Nat) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg)
      (monadLift getDev : Leanux.M Device) := native _ confirmed (native_store getDev_sameWGStore confirmed)

private theorem modifyEnv_spec (f : EnvWorld → EnvWorld) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg) (modifyEnv f) := by
  unfold modifyEnv
  apply hoare_modify
  exact fun _ hi => hi

private theorem idle (confirmed : List Nat) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg) Env.requireIdleDevice :=
  store _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store) confirmed

private theorem up_source (confirmed : List Nat) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg) Env.wgUp := by
  have up := native _ confirmed (up_native confirmed)
  have get := readWG confirmed
  have effect {α : Type} (a : AmbientM α) := ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  have env (f : EnvWorld → EnvWorld) := modifyEnv_spec f confirmed
  routing_tx_source [Env.wgUp,skipCut] using [up,get,effect,route,env]

private theorem down_source (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg) Env.wgDown := by
  have down := native _ confirmed (down_native H1 confirmed)
  have get := readWG confirmed
  have stopped := idle confirmed
  have effect {α : Type} (a : AmbientM α) := ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  routing_tx_source [Env.wgDown,skipCut,modifyRouting] using [down,get,stopped,effect,route]

private theorem delete_source (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg) Env.wgDelete := by
  have down := native _ confirmed (down_native H1 confirmed)
  have destruct := native _ confirmed (destruct_native H1 confirmed)
  have get := readWG confirmed
  have dev := readDev confirmed
  have stopped := idle confirmed
  have slept := native _ confirmed (native_store mayHaveSlept_sameWGStore confirmed)
  have inet := store _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store) confirmed
  have effect {α : Type} (a : AmbientM α) := ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  routing_tx_source [Env.wgDelete,WG.wgDelete,skipCut,modifyRouting,unsupported]
    using [down,destruct,get,dev,stopped,slept,inet,effect,route]

private theorem cleanup_source (confirmed : List Nat) :
    Framing.Preserves (fun w : World => History.Native confirmed w.wg) Env.netnsCleanup := by
  have preExit := native _ confirmed (preExit_native confirmed)
  have effect {α : Type} (a : AmbientM α) := ambient a confirmed
  have route {α : Type} (a : Net.M α) := routing a confirmed
  have env (f : EnvWorld → EnvWorld) := modifyEnv_spec f confirmed
  routing_tx_source [Env.netnsCleanup,Env.runWorker,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effect,route,env]

theorem up : Joint.Preserves (RxHistory.audit envWgUpAudit) :=
  Joint.from_global _ PublicationControls.up (Global.audited _ _ envWgUpAudit_erases up_source)

theorem down (H1 : H1ResponderCurrentEdges) : Joint.Preserves (RxHistory.audit envWgDownAudit) :=
  Joint.from_global _ PublicationControls.down (Global.audited _ _ envWgDownAudit_erases (down_source H1))

theorem delete (H1 : H1ResponderCurrentEdges) : Joint.Preserves (RxHistory.audit envWgDeleteAudit) :=
  Joint.from_global _ PublicationControls.delete (Global.audited _ _ envWgDeleteAudit_erases (delete_source H1))

theorem netnsCleanup : Joint.Preserves (RxHistory.audit envNetnsCleanupAudit) :=
  Joint.from_global _ PublicationControls.netnsCleanup
    (Global.audited _ _ envNetnsCleanupAudit_erases cleanup_source)

theorem scalar (confirmed : List Nat) (w v : World) (same : envScalarView v = envScalarView w)
    (hi : History.Native confirmed w.wg) : History.Native confirmed v.wg := by
  have curr := congrArg (fun s : ProductStore43 => current {dev := s.2.2.2.dev}) same
  have fields := congrArg (fun s : ProductStore43 => CurrentSlots.fields {dev := s.2.2.2.dev}) same
  refine ⟨hi.1.frame ?_, CurrentSlots.fields_transport hi.2 ?_⟩
  · funext pid
    cases hv : v.wg.dev <;> cases hw : w.wg.dev
    all_goals first
      | (solve | simp [current, hv, hw])
      | simpa [current, envScalarView, envScalarStore, productStoreView,
          envScalarDevice, wgStoreView, hv, hw] using congrFun curr pid
  · unfold CurrentSlots.fields RxCredits.keyWords at fields ⊢
    simpa only [envScalarView, envScalarStore, productStoreView,
      envScalarDevice, wgStoreView, Option.map_map, Option.bind_map, Function.comp_def] using fields

theorem mtu (n : Nat) : Joint.Preserves (RxHistory.audit (setMtuAudit n)) := by
  apply Joint.from_global _ (PublicationControls.mtu n)
  apply Global.audited _ _ (setMtuAudit_erases n)
  intro confirmed
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact scalar confirmed w v ((ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w x v run) hi

theorem create : Joint.Preserves (RxHistory.mixed (liftWGObserver wgCreatePrefix)) :=
  Joint.from_global _ PublicationControls.create
    (Global.native_mixed _ _ wgCreatePrefix_erases create_native)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Controls
