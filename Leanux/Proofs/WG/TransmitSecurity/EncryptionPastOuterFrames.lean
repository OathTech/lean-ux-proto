import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastControls
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginOuterFrames
import Leanux.Proofs.WG.Queues.TxLiveDump

/-! Native non-encryption dispatcher paths preserve historical exclusion.
Descriptor and route operations frame the projection; dump and lifecycle
operations use their concrete native contracts. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.OuterNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration

theorem native_store (h : List (Option Nat × SkbId)) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : Ready h [] w.wg) :
    Ready h [] v.wg := by
  have device := congrArg WGStoreView.dev same
  have epochs := congrArg WGStoreView.netIfindexNext same
  change v.wg.dev = w.wg.dev at device
  change v.wg.netIfindexNext = w.wg.netIfindexNext at epochs
  simpa only [Ready,TxDisposition.LiveFrontier.Ready,TxDisposition.LiveFrontier.Inv,
    TxDisposition.LiveFrontier.Physical,view,device,epochs] using hi

private theorem product_stable (a : Leanux.M α) (frame : SameProductStore a) (h : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready h [] w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact EncryptionPast.product_transport ((ProjectedAction.iff_run _ _ _).mp frame w x v hr) hi

theorem fs (a : FS.M α) (h : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready h [] w.wg) (liftFS a) :=
  productFS_spec a _ (fun _ _ _ _ hi => hi)

theorem task (a : TaskM α) (h : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready h [] w.wg) (liftTask a) :=
  productTask_spec a _ (fun _ _ _ hi => hi)

theorem seccomp (a : Seccomp.M α) (h : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready h [] w.wg) (liftSeccomp a) :=
  productSeccomp_spec a _ (fun _ _ _ _ hi => hi)

theorem outer_get (h : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready h [] w.wg) (get : Leanux.M World) :=
  hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2)

theorem outer_edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg)
    (h : List (Option Nat × SkbId)) : Preserves (fun w : World => Ready h [] w.wg) (_root_.modify f : Leanux.M Unit) :=
  hoare_modify _ (fun w hi => native_store h w (f w) (same w) hi)

private theorem outer_ambient (a : AmbientM α) (h : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready h [] w.wg) (monadLift a : Leanux.M α) :=
  productAmbient_spec a _ (fun _ _ hi => hi)

private theorem outer_route (a : Net.M α) (h : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready h [] w.wg) (monadLift a : Leanux.M α) :=
  product_stable _ (fun s => productRouting_spec a (fun t => t = s)) h

theorem native_socket (fd : Nat) (body : Leanux.M Int) (h : List (Option Nat × SkbId))
    (hb : Preserves (fun w : World => Ready h [] w.wg) body) :
    Preserves (fun w : World => Ready h [] w.wg) (Leanux.socketCallOn fd body) := by
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => Ready h [] w.wg) (monadLift a : Leanux.M α) := fs a h
  routing_tx_source [Leanux.socketCallOn] using [hb,files]

theorem native_netlink (body : Leanux.M Int) (h : List (Option Nat × SkbId))
    (hb : Preserves (fun w : World => Ready h [] w.wg) body) :
    Preserves (fun w : World => Ready h [] w.wg) (Leanux.netlinkRequest body) := by
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => Ready h [] w.wg) (monadLift a : Leanux.M α) := fs a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Leanux.netlinkRequest,Leanux.socketCall,Leanux.socketCallOn,skipCut] using [hb,files,ambient]

theorem native_rtnetlink (body : Leanux.M Int) (h : List (Option Nat × SkbId))
    (hb : Preserves (fun w : World => Ready h [] w.wg) body) :
    Preserves (fun w : World => Ready h [] w.wg) (Leanux.rtnetlinkRequest body) := by
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => Ready h [] w.wg) (monadLift a : Leanux.M α) := fs a h
  have tasks {α : Type} (a : TaskM α) : Preserves (fun w : World => Ready h [] w.wg) (monadLift a : Leanux.M α) := fs (monadLift a : FS.M α) h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  have read := outer_get h
  have edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) := outer_edit f same h
  routing_tx_source [Leanux.rtnetlinkRequest,Leanux.socketCallOn,skipCut,unsupported] using [hb,files,tasks,ambient,read]
  all_goals exact edit _ (fun _ => rfl)

theorem add_route (dst plen oif typeCode metric mtu nlflags : Nat) (h : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready h [] w.wg) (Env.wgAddroute dst plen oif typeCode metric mtu nlflags) := by
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgAddroute,invariant] using [routes,ambient]

theorem add_addr (addr plen : Nat) (h : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready h [] w.wg) (Env.wgAddaddr addr plen) := by
  have read : Preserves (fun w : World => Ready h [] w.wg) (getWG : Leanux.M WGWorld) :=
    product_stable _ (fun s => productGetWG_spec (fun t => t = s)) h
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgAddaddr,getRouting,modifyRouting,unsupported] using [read,routes,ambient]

theorem del_route (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) (h : List (Option Nat × SkbId)) :
    Preserves (fun w : World => Ready h [] w.wg) (Env.wgDelroute family named dst plen oif typeCode metric) := by
  have read : Preserves (fun w : World => Ready h [] w.wg) (getWG : Leanux.M WGWorld) :=
    product_stable _ (fun s => productGetWG_spec (fun t => t = s)) h
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgDelroute,getRouting,modifyRouting,unsupported] using [read,routes,ambient]

set_option maxHeartbeats 600000 in
theorem quiet_dispatch (call : Syscall) (h : List (Option Nat × SkbId))
    (retained : DispatchRetained call) (notUp : call ≠ .wgUp) :
    Preserves (fun w : World => Ready h [] w.wg) (Leanux.dispatch call) := by
  have native {α : Type} (a : WG.M α) (safe : Preserves (fun w => Ready h [] w) a) :
      Preserves (fun w : World => Ready h [] w.wg) (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product _ _ safe
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => Ready h [] w.wg) (monadLift a : Leanux.M α) := fs a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  have gd (ref : DeviceRef) := native _ (ready_frame (TxDisposition.LiveFrontier.dump_device ref) (Dump.dump_device_view ref))
  have gs (fd : Nat) := native _ (ready_store ((getNlSock_sameWGWorld fd).factor wgStoreView))
  have ss (fd : Nat) (sock : NlSock) := native _ (ready_frame (TxDisposition.LiveFrontier.dump_frame (setNlSock_sameDump fd sock)) (Dump.dump_view (setNlSock_sameDump fd sock)))
  have ds (fd : Nat) (ref : DeviceRef) := native _ (ready_frame (TxDisposition.LiveFrontier.dump_start fd ref) (Dump.dump_start_view fd ref))
  have dr (fd : Nat) := native _ (ready_frame (TxDisposition.LiveFrontier.dump_recv fd) (Dump.dump_recv_view fd))
  have advance (ticks : Nat) := product_stable _ (advance_sameKernel ticks) h
  cases call <;> simp only [DispatchRetained] at retained
  all_goals try contradiction
  case wgSetMtu n => exact native_socket _ _ h (Controls.env_mtu n)
  case wgDown => exact native_socket _ _ h (Controls.env_down h)
  case wgDeladdr family => exact native_rtnetlink _ h (product_stable _ (wgDeladdr_sameKernel family) h)
  case wgDelroute family named dst plen oif typeCode metric =>
    exact native_rtnetlink _ h (del_route family named dst plen oif typeCode metric h)
  case wgAddroute dst plen oif typeCode metric mtu nlflags =>
    exact native_rtnetlink _ h (add_route dst plen oif typeCode metric mtu nlflags h)
  case wgAddaddr addr plen => exact native_rtnetlink _ h (add_addr addr plen h)
  case wgNetnsClose =>
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi run
    exact native_store h w v ((ProjectedAction.iff_run _ _ _).mp SyscallFrames.netnsClose_sameWGStore w x v run) hi
  case wgGet ref =>
    apply native_netlink _ h
    routing_tx_source [modifyAmbient] using [gd,ambient]
    all_goals exact outer_edit _ (fun _ => rfl) h
  case wgGetStart ref =>
    apply native_socket _ _ h
    routing_tx_source [skipCut,skipCutExactly] using [gs,ss,ds,ambient]
  case wgGetRecv =>
    apply native_socket _ _ h
    routing_tx_source [skipCut,unsupported,modifyAmbient] using [dr,ambient]
    all_goals exact outer_edit _ (fun _ => rfl) h
  case wgAdvance ticks =>
    dsimp only [Leanux.dispatch]
    routing_tx_source [unsupported] using [files,advance,ambient]
  case seccompProbe nr args target strict => cases target <;> exact seccomp _ h
  case seccompInstall => exact seccomp _ h
  case seccompPrctl => exact seccomp _ h
  case seccompCapdrop => exact seccomp _ h
  case seccompQuery => exact seccomp _ h
  all_goals exact fs _ h

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.OuterNative
