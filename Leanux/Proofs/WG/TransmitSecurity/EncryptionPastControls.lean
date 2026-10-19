import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastDumpFrames
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginControlFrames
import Leanux.Proofs.WG.Queues.TxLiveControls

/-! Native environment deletion, namespace cleanup and MTU changes preserve
historical encryption exclusion at empty-active caller boundaries. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Controls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

private theorem native (a : WG.M α) (past : List (Option Nat × SkbId))
    (safe : Preserves (fun w => Ready past [] w) a) :
    Preserves (fun w : World => Ready past [] w.wg) (monadLift a : Leanux.M α) :=
  PublicationPoll.native_product _ _ safe

private theorem product_store_frame (a : Leanux.M α) (frame : SameProductStore a) (past : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready past [] w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact EncryptionPast.product_transport ((ProjectedAction.iff_run _ _ _).mp frame w x v hr) hi

private theorem effect (a : AmbientM α) (past : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready past [] w.wg) (monadLift a : Leanux.M α) :=
  productAmbient_spec a _ (fun _ _ hi => hi)

private theorem route (a : Net.M α) (past : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready past [] w.wg) (monadLift a : Leanux.M α) :=
  product_store_frame _ (fun s => productRouting_spec a (fun t => t = s)) past

private theorem readWG (past : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready past [] w.wg) (getWG : Leanux.M WGWorld) :=
  product_store_frame _ (fun s => productGetWG_spec (fun t => t = s)) past

private theorem readDev (past : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready past [] w.wg) (monadLift getDev : Leanux.M Device) :=
  native _ past (ready_store getDev_sameWGStore)

private theorem editEnv (f : EnvWorld → EnvWorld) (past : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready past [] w.wg) (modifyEnv f) := by
  unfold modifyEnv
  apply hoare_modify
  exact fun _ hi => hi

private theorem idle (past : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready past [] w.wg) Env.requireIdleDevice :=
  product_store_frame _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store) past

theorem env_down (past : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready past [] w.wg) Env.wgDown := by
  have down := native _ past (Removal.down)
  have get := readWG past
  have stopped := idle past
  have effects {α : Type} (a : AmbientM α) := effect a past
  have routes {α : Type} (a : Net.M α) := route a past
  routing_tx_source [Env.wgDown,skipCut,modifyRouting] using [down,get,stopped,effects,routes]

theorem env_delete (past : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready past [] w.wg) Env.wgDelete := by
  have down := native _ past (Removal.down)
  have destruct := native _ past (DeviceLifecycle.device_destruct)
  have get := readWG past
  have dev := readDev past
  have stopped := idle past
  have slept := native _ past (ready_store mayHaveSlept_sameWGStore)
  have inet := product_store_frame _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store) past
  have effects {α : Type} (a : AmbientM α) := effect a past
  have routes {α : Type} (a : Net.M α) := route a past
  routing_tx_source [Env.wgDelete,WG.wgDelete,skipCut,modifyRouting,unsupported]
    using [down,destruct,get,dev,stopped,slept,inet,effects,routes]

theorem pre_exit : Preserves (Ready past []) WG.netnsPreExit := by
  unfold WG.netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketReinit; exact Removal.socket_reinit _ _)
    | (rx_retention_head clearPeerEndpointSrc; exact DeviceConfiguration.clear_endpoint _)
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
    | encryption_past_handshake_step

theorem env_cleanup (past : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready past [] w.wg) Env.netnsCleanup := by
  have preExit := native _ past (pre_exit)
  have effects {α : Type} (a : AmbientM α) := effect a past
  have routes {α : Type} (a : Net.M α) := route a past
  have env (f : EnvWorld → EnvWorld) := editEnv f past
  routing_tx_source [Env.netnsCleanup,Env.runWorker,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effects,routes,env]

theorem env_mtu (n : Nat) : Preserves (fun w : World => Ready past [] w.wg) (Env.setMtu n) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v before run
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w x v run
  have field := congrArg (fun s : ProductStore43 =>
    view {dev:=s.2.2.2.dev,netIfindexNext:=s.2.2.2.netIfindexNext}) same
  have equal : view v.wg = view w.wg := by
    simpa only [view,envScalarView,envScalarStore,envScalarDevice,productStoreView,
      wgStoreView,Option.map_map,Function.comp_def] using field
  exact ⟨(hoare_iff_run _ _ _).mp (TxDisposition.LiveFrontier.env_mtu n)
    w x v before.1 run,equal ▸ before.2⟩

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Controls
