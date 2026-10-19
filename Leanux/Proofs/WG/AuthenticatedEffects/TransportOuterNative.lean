import Leanux.Proofs.WG.AuthenticatedEffects.TransportDumpFrames
import Leanux.Proofs.WG.AuthenticatedEffects.TransportControlFrames
import Leanux.Proofs.WG.Lifetimes.DispatchSource
import Leanux.Proofs.Framing.Syscalls

/-! Typed non-eventful dispatcher paths retain live packet certificates.
Each changing WG operation has its concrete native frame or deletion proof. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportOuterNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration

theorem native_store (h : List TransportDriver.OriginEvent) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : TransportPublication.Inv h w.wg) :
    TransportPublication.Inv h v.wg := by
  have dev := congrArg WGStoreView.dev same
  change v.wg.dev = w.wg.dev at dev
  exact hi.sameRx (by simp only [RxDisposition.nativeRxStore,dev])

private theorem product_stable (a : Leanux.M α) (frame : SameProductStore a) (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  have same := congrArg (fun s : ProductStore43 => s.2.2.2.dev)
    ((ProjectedAction.iff_run _ _ _).mp frame w x v hr)
  change v.wg.dev = w.wg.dev at same
  exact hi.sameRx (by simp only [RxDisposition.nativeRxStore,same])

theorem fs (a : FS.M α) (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (liftFS a) :=
  productFS_spec a _ (fun _ _ _ _ hi => hi)

theorem task (a : TaskM α) (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (liftTask a) :=
  productTask_spec a _ (fun _ _ _ hi => hi)

theorem seccomp (a : Seccomp.M α) (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (liftSeccomp a) :=
  productSeccomp_spec a _ (fun _ _ _ _ hi => hi)

theorem outer_get (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (get : Leanux.M World) :=
  hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2)

theorem outer_edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg)
    (h : List TransportDriver.OriginEvent) : Preserves (fun w : World => TransportPublication.Inv h w.wg) (modify f : Leanux.M Unit) :=
  hoare_modify _ (fun w hi => native_store h w (f w) (same w) hi)

private theorem outer_ambient (a : AmbientM α) (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (monadLift a : Leanux.M α) :=
  productAmbient_spec a _ (fun _ _ hi => hi)

private theorem outer_route (a : Net.M α) (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (monadLift a : Leanux.M α) :=
  product_stable _ (fun s => productRouting_spec a (fun t => t = s)) h

theorem native_socket (fd : Nat) (body : Leanux.M Int) (h : List TransportDriver.OriginEvent)
    (hb : Preserves (fun w : World => TransportPublication.Inv h w.wg) body) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (Leanux.socketCallOn fd body) := by
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => TransportPublication.Inv h w.wg) (monadLift a : Leanux.M α) := fs a h
  routing_tx_source [Leanux.socketCallOn] using [hb,files]

theorem native_netlink (body : Leanux.M Int) (h : List TransportDriver.OriginEvent)
    (hb : Preserves (fun w : World => TransportPublication.Inv h w.wg) body) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (Leanux.netlinkRequest body) := by
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => TransportPublication.Inv h w.wg) (monadLift a : Leanux.M α) := fs a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Leanux.netlinkRequest,Leanux.socketCall,Leanux.socketCallOn,skipCut] using [hb,files,ambient]

theorem native_rtnetlink (body : Leanux.M Int) (h : List TransportDriver.OriginEvent)
    (hb : Preserves (fun w : World => TransportPublication.Inv h w.wg) body) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (Leanux.rtnetlinkRequest body) := by
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => TransportPublication.Inv h w.wg) (monadLift a : Leanux.M α) := fs a h
  have tasks {α : Type} (a : TaskM α) : Preserves (fun w : World => TransportPublication.Inv h w.wg) (monadLift a : Leanux.M α) := fs (monadLift a : FS.M α) h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  have read := outer_get h
  have edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) := outer_edit f same h
  routing_tx_source [Leanux.rtnetlinkRequest,Leanux.socketCallOn,skipCut,unsupported] using [hb,files,tasks,ambient,read]
  all_goals exact edit _ (fun _ => rfl)

theorem dump_rx (a : WG.M α) (frame : SameDump a) : SameView RxDisposition.nativeRxStore a := by
  apply frame.of_factor
    (fun s : WGStoreView => (s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?)) _
  intro w
  rfl

theorem add_route (dst plen oif typeCode metric mtu nlflags : Nat) (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (Env.wgAddroute dst plen oif typeCode metric mtu nlflags) := by
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgAddroute,invariant] using [routes,ambient]

theorem add_addr (addr plen : Nat) (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (Env.wgAddaddr addr plen) := by
  have read : Preserves (fun w : World => TransportPublication.Inv h w.wg) (getWG : Leanux.M WGWorld) :=
    product_stable _ (fun s => productGetWG_spec (fun t => t = s)) h
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgAddaddr,getRouting,modifyRouting,unsupported] using [read,routes,ambient]

theorem del_route (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (Env.wgDelroute family named dst plen oif typeCode metric) := by
  have read : Preserves (fun w : World => TransportPublication.Inv h w.wg) (getWG : Leanux.M WGWorld) :=
    product_stable _ (fun s => productGetWG_spec (fun t => t = s)) h
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgDelroute,getRouting,modifyRouting,unsupported] using [read,routes,ambient]

set_option maxHeartbeats 600000 in
theorem quiet_dispatch (call : Syscall) (h : List TransportDriver.OriginEvent)
    (retained : DispatchRetained call) (notUp : call ≠ .wgUp) :
    Preserves (fun w : World => TransportPublication.Inv h w.wg) (Leanux.dispatch call) := by
  have native {α : Type} (a : WG.M α) (safe : Preserves (fun w => TransportPublication.Inv h w) a) :
      Preserves (fun w : World => TransportPublication.Inv h w.wg) (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product _ _ safe
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => TransportPublication.Inv h w.wg) (monadLift a : Leanux.M α) := fs a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  have gd (ref : DeviceRef) := native _ (TransportPublication.preserves_of_rx _ ((TransportDump.wgGetDevice_geometry ref).factor Prod.snd) h)
  have gs (fd : Nat) := native _ (TransportPublication.preserves_of_rx _ ((getNlSock_sameWGWorld fd).factor RxDisposition.nativeRxStore) h)
  have ss (fd : Nat) (sock : NlSock) := native _ (TransportPublication.preserves_of_rx _ (dump_rx _ (setNlSock_sameDump fd sock)) h)
  have ds (fd : Nat) (ref : DeviceRef) := native _ (TransportPublication.preserves_of_rx _ ((TransportDump.netlinkDumpStart_geometry fd ref).factor Prod.snd) h)
  have dr (fd : Nat) := native _ (TransportPublication.preserves_of_rx _ ((TransportDump.netlinkRecvmsg_geometry fd).factor Prod.snd) h)
  have advance (ticks : Nat) := product_stable _ (advance_sameKernel ticks) h
  cases call <;> simp only [DispatchRetained] at retained
  all_goals try contradiction
  case wgSetMtu n => exact native_socket _ _ h (TransportControl.env_mtu n h)
  case wgDown => exact native_socket _ _ h (TransportControl.env_down h)
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

end Leanux.Proofs.WG.AuthenticatedEffects.TransportOuterNative
