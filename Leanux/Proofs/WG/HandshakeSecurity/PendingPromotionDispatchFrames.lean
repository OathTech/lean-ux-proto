import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverDispatchFrames
import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionOuter
import Leanux.Proofs.WG.HandshakeSecurity.ResponderControls
import Leanux.Proofs.Framing.Syscalls

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion.DispatchFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration

theorem carrier_wg_store (h : List Nat) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : Carrier h w.wg) : Carrier h v.wg := by
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  have counter : v.wg.keypairCounter = w.wg.keypairCounter := congrArg WGStoreView.keypairCounter same
  refine ⟨?_,CurrentSlots.fields_transport hi.2.1 ?_,hi.2.2.retained ?_⟩
  · intro s hs
    apply hi.1 s
    simpa only [ConfiguredIdentity.view,device] using hs
  · unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]
  · have keys : keypairResidents v.wg = keypairResidents w.wg := by
      funext kid; simp only [keypairResidents,device]
    have projection : view v.wg = view w.wg := by simp only [view,nextSlot,keys,device,counter]
    rw [projection]
    exact Retained.refl _

theorem carrier_env_mtu (n : Nat) (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (Env.setMtu n) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  have bounds := (hoare_iff_run _ _ _).mp
    (ResidentMaterial.bounds_forget_product (Responder.DriverCuts.Frames.carrier_env_mtu n))
      w x v ⟨hi.1,hi.2.1⟩ run
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w x v run
  refine ⟨bounds.1,bounds.2,hi.2.2.retained ?_⟩
  have project := congrArg (fun s : ProductStore43 =>
    view {dev:=s.2.2.2.dev,keypairCounter:=s.2.2.2.keypairCounter}) same
  have factor (world : World) :
      view {dev := (envScalarView world).2.2.2.dev, keypairCounter := (envScalarView world).2.2.2.keypairCounter} = view world.wg := by
    have keys : keypairResidents {dev := (envScalarView world).2.2.2.dev, keypairCounter := (envScalarView world).2.2.2.keypairCounter} = keypairResidents world.wg := by
      funext kid
      simp only [keypairResidents,envScalarView,envScalarStore,productStoreView,
        wgStoreView,Option.bind_map,Function.comp_def,envScalarDevice]
    apply Store.ext
    · rfl
    · funext pid
      simp only [view,nextSlot,envScalarView,envScalarStore,productStoreView,
        wgStoreView,Option.bind_map,Function.comp_def,envScalarDevice]
      exact congrArg (fun f => ((world.wg.dev.bind fun d => d.peers[pid]?).bind Peer.keypairNext).bind f) keys
  have projected : view v.wg = view w.wg := (factor v).symm.trans (project.trans (factor w))
  rw [projected]
  exact Retained.refl _

private theorem product_stable (a : Leanux.M α) (frame : SameProductStore a) (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact carrier_wg_store h w v (congrArg (fun s : ProductStore43 => s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w x v hr)) hi

theorem fs (a : FS.M α) (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (liftFS a) :=
  productFS_spec a _ (fun _ _ _ _ hi => hi)

theorem task (a : TaskM α) (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (liftTask a) :=
  productTask_spec a _ (fun _ _ _ hi => hi)

theorem seccomp (a : Seccomp.M α) (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (liftSeccomp a) :=
  productSeccomp_spec a _ (fun _ _ _ _ hi => hi)

theorem outer_get (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (get : Leanux.M World) :=
  hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2)

theorem outer_edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg)
    (h : List Nat) : Framing.Preserves (fun w : World => Carrier h w.wg) (modify f : Leanux.M Unit) :=
  hoare_modify _ (fun w hi => carrier_wg_store h w (f w) (same w) hi)

private theorem outer_ambient (a : AmbientM α) (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) :=
  productAmbient_spec a _ (fun _ _ hi => hi)

private theorem outer_route (a : Net.M α) (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) :=
  product_stable _ (fun s => productRouting_spec a (fun t => t = s)) h

theorem native_socket (fd : Nat) (body : Leanux.M Int) (h : List Nat)
    (hb : Framing.Preserves (fun w : World => Carrier h w.wg) body) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (Leanux.socketCallOn fd body) := by
  have files {α : Type} (a : FS.M α) : Framing.Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) := fs a h
  routing_tx_source [Leanux.socketCallOn] using [hb,files]

theorem native_netlink (body : Leanux.M Int) (h : List Nat)
    (hb : Framing.Preserves (fun w : World => Carrier h w.wg) body) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (Leanux.netlinkRequest body) := by
  have files {α : Type} (a : FS.M α) : Framing.Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) := fs a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Leanux.netlinkRequest,Leanux.socketCall,Leanux.socketCallOn,skipCut] using [hb,files,ambient]

theorem native_rtnetlink (body : Leanux.M Int) (h : List Nat)
    (hb : Framing.Preserves (fun w : World => Carrier h w.wg) body) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (Leanux.rtnetlinkRequest body) := by
  have files {α : Type} (a : FS.M α) : Framing.Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) := fs a h
  have tasks {α : Type} (a : TaskM α) : Framing.Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) := fs (monadLift a : FS.M α) h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  have read := outer_get h
  have edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) := outer_edit f same h
  routing_tx_source [Leanux.rtnetlinkRequest,Leanux.socketCallOn,skipCut,unsupported] using [hb,files,tasks,ambient,read]
  all_goals exact edit _ (fun _ => rfl)

theorem add_route (dst plen oif typeCode metric mtu nlflags : Nat) (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (Env.wgAddroute dst plen oif typeCode metric mtu nlflags) := by
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgAddroute,invariant] using [routes,ambient]

theorem add_addr (addr plen : Nat) (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (Env.wgAddaddr addr plen) := by
  have read : Framing.Preserves (fun w : World => Carrier h w.wg) (getWG : Leanux.M WGWorld) :=
    product_stable _ (fun s => productGetWG_spec (fun t => t = s)) h
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgAddaddr,getRouting,modifyRouting,unsupported] using [read,routes,ambient]

theorem del_route (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) (h : List Nat) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (Env.wgDelroute family named dst plen oif typeCode metric) := by
  have read : Framing.Preserves (fun w : World => Carrier h w.wg) (getWG : Leanux.M WGWorld) :=
    product_stable _ (fun s => productGetWG_spec (fun t => t = s)) h
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgDelroute,getRouting,modifyRouting,unsupported] using [read,routes,ambient]

set_option maxHeartbeats 600000 in
theorem quiet_dispatch (frames : H1LifecycleFrames) (call : Syscall) (h : List Nat)
    (retained : DispatchRetained call) (notUp : call ≠ .wgUp) :
    Framing.Preserves (fun w : World => Carrier h w.wg) (Leanux.dispatch call) := by
  have native {α : Type} (a : WG.M α) (safe : Framing.Preserves (Carrier h) a) :
      Framing.Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product _ _ safe
  have files {α : Type} (a : FS.M α) : Framing.Preserves (fun w : World => Carrier h w.wg) (monadLift a : Leanux.M α) := fs a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  have gd (ref : DeviceRef) := native _ (Dump.wgGetDevice_preserves ref h)
  have gs (fd : Nat) := native _ ((getNlSock_sameWGWorld fd).wp (Carrier h))
  have ss (fd : Nat) (sock : NlSock) := native _ (Dump.dump_preserves _ (setNlSock_sameDump fd sock) h)
  have ds (fd : Nat) (ref : DeviceRef) := native _ (Dump.netlinkDumpStart_preserves fd ref h)
  have dr (fd : Nat) := native _ (Dump.netlinkRecvmsg_preserves fd h)
  have advance (ticks : Nat) := product_stable _ (advance_sameKernel ticks) h
  cases call <;> simp only [DispatchRetained] at retained
  all_goals try contradiction
  case wgSetMtu n => exact native_socket _ _ h (carrier_env_mtu n h)
  case wgDown => exact native_socket _ _ h (Environment.down frames h)
  case wgDeladdr family => exact native_rtnetlink _ h (product_stable _ (wgDeladdr_sameKernel family) h)
  case wgDelroute family named dst plen oif typeCode metric =>
    exact native_rtnetlink _ h (del_route family named dst plen oif typeCode metric h)
  case wgAddroute dst plen oif typeCode metric mtu nlflags =>
    exact native_rtnetlink _ h (add_route dst plen oif typeCode metric mtu nlflags h)
  case wgAddaddr addr plen => exact native_rtnetlink _ h (add_addr addr plen h)
  case wgNetnsClose =>
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi run
    exact carrier_wg_store h w v
      ((ProjectedAction.iff_run _ _ _).mp SyscallFrames.netnsClose_sameWGStore w x v run) hi
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

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion.DispatchFrames
