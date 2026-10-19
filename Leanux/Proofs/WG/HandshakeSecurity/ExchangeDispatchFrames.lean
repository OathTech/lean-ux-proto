import Leanux.Proofs.WG.HandshakeSecurity.ExchangeOuter
import Leanux.Proofs.Framing.Syscalls

namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange.DispatchFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration

theorem carrier_wg_store (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : ProductInv h w) : ProductInv h v :=
  product_wg_stable h w v same hi

theorem carrier_env_mtu (n : Nat) (h : List Event) :
    Framing.Preserves (ProductInv h) (Env.setMtu n) := by
  apply frame_product h _
  intro w value v run
  have tags := (ProjectedAction.iff_run _ _ _).mp
    ((setMtu_sameEnvScalar n).of_factor
      (fun s : ProductStore43 => fun pid : PeerId =>
        (s.2.2.2.dev.bind fun d => d.peers[pid]?).map Peer.handshakeState)
      (fun w : World => handshakeTagAt w.wg) (by
        intro w
        change handshakeTagAt w.wg = (fun pid =>
          ((w.wg.dev.map envScalarDevice).bind fun d => d.peers[pid]?).map Peer.handshakeState)
        unfold handshakeTagAt
        cases w.wg.dev <;> rfl)) w value v run
  intro pid tag found _
  exact (congrFun tags pid).symm.trans found

private theorem product_stable (a : Leanux.M α) (frame : SameProductStore a) (h : List Event) :
    Framing.Preserves (ProductInv h) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact carrier_wg_store h w v (congrArg (fun s : ProductStore43 => s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w x v hr)) hi

theorem fs (a : FS.M α) (h : List Event) :
    Framing.Preserves (ProductInv h) (liftFS a) :=
  productFS_spec a _ (fun _ _ _ _ hi => hi)

theorem task (a : TaskM α) (h : List Event) :
    Framing.Preserves (ProductInv h) (liftTask a) :=
  productTask_spec a _ (fun _ _ _ hi => hi)

theorem seccomp (a : Seccomp.M α) (h : List Event) :
    Framing.Preserves (ProductInv h) (liftSeccomp a) :=
  productSeccomp_spec a _ (fun _ _ _ _ hi => hi)

theorem outer_get (h : List Event) :
    Framing.Preserves (ProductInv h) (get : Leanux.M World) :=
  hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2)

theorem outer_edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg)
    (h : List Event) : Framing.Preserves (ProductInv h) (modify f : Leanux.M Unit) :=
  hoare_modify _ (fun w hi => carrier_wg_store h w (f w) (same w) hi)

private theorem outer_ambient (a : AmbientM α) (h : List Event) :
    Framing.Preserves (ProductInv h) (monadLift a : Leanux.M α) :=
  productAmbient_spec a _ (fun _ _ hi => hi)

private theorem outer_route (a : Net.M α) (h : List Event) :
    Framing.Preserves (ProductInv h) (monadLift a : Leanux.M α) :=
  product_stable _ (fun s => productRouting_spec a (fun t => t = s)) h

theorem native_socket (fd : Nat) (body : Leanux.M Int) (h : List Event)
    (hb : Framing.Preserves (ProductInv h) body) :
    Framing.Preserves (ProductInv h) (Leanux.socketCallOn fd body) := by
  have files {α : Type} (a : FS.M α) : Framing.Preserves (ProductInv h) (monadLift a : Leanux.M α) := fs a h
  routing_tx_source [Leanux.socketCallOn] using [hb,files]

theorem native_netlink (body : Leanux.M Int) (h : List Event)
    (hb : Framing.Preserves (ProductInv h) body) :
    Framing.Preserves (ProductInv h) (Leanux.netlinkRequest body) := by
  have files {α : Type} (a : FS.M α) : Framing.Preserves (ProductInv h) (monadLift a : Leanux.M α) := fs a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Leanux.netlinkRequest,Leanux.socketCall,Leanux.socketCallOn,skipCut] using [hb,files,ambient]

theorem native_rtnetlink (body : Leanux.M Int) (h : List Event)
    (hb : Framing.Preserves (ProductInv h) body) :
    Framing.Preserves (ProductInv h) (Leanux.rtnetlinkRequest body) := by
  have files {α : Type} (a : FS.M α) : Framing.Preserves (ProductInv h) (monadLift a : Leanux.M α) := fs a h
  have tasks {α : Type} (a : TaskM α) : Framing.Preserves (ProductInv h) (monadLift a : Leanux.M α) := fs (monadLift a : FS.M α) h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  have read := outer_get h
  have edit (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) := outer_edit f same h
  routing_tx_source [Leanux.rtnetlinkRequest,Leanux.socketCallOn,skipCut,unsupported] using [hb,files,tasks,ambient,read]
  all_goals exact edit _ (fun _ => rfl)

theorem add_route (dst plen oif typeCode metric mtu nlflags : Nat) (h : List Event) :
    Framing.Preserves (ProductInv h) (Env.wgAddroute dst plen oif typeCode metric mtu nlflags) := by
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgAddroute,invariant] using [routes,ambient]

theorem add_addr (addr plen : Nat) (h : List Event) :
    Framing.Preserves (ProductInv h) (Env.wgAddaddr addr plen) := by
  have read : Framing.Preserves (ProductInv h) (getWG : Leanux.M WGWorld) :=
    product_stable _ (fun s => productGetWG_spec (fun t => t = s)) h
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgAddaddr,getRouting,modifyRouting,unsupported] using [read,routes,ambient]

theorem del_route (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) (h : List Event) :
    Framing.Preserves (ProductInv h) (Env.wgDelroute family named dst plen oif typeCode metric) := by
  have read : Framing.Preserves (ProductInv h) (getWG : Leanux.M WGWorld) :=
    product_stable _ (fun s => productGetWG_spec (fun t => t = s)) h
  have routes {α : Type} (a : Net.M α) := outer_route a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  routing_tx_source [Env.wgDelroute,getRouting,modifyRouting,unsupported] using [read,routes,ambient]

set_option maxHeartbeats 600000 in
theorem quiet_dispatch (traffic : H1TrafficTagFrames) (call : Syscall) (h : List Event)
    (retained : DispatchRetained call) (notUp : call ≠ .wgUp) (notDown : call ≠ .wgDown) :
    Framing.Preserves (ProductInv h) (Leanux.dispatch call) := by
  have native {α : Type} (a : WG.M α) (safe : Framing.Preserves (StateInv h) a) :
      Framing.Preserves (ProductInv h) (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product _ _ safe
  have files {α : Type} (a : FS.M α) : Framing.Preserves (ProductInv h) (monadLift a : Leanux.M α) := fs a h
  have ambient {α : Type} (a : AmbientM α) := outer_ambient a h
  have gd (ref : DeviceRef) : Framing.Preserves (ProductInv h) (monadLift (wgGetDevice ref) : Leanux.M (Except Int Lean.Json)) := native _ (frame h _ (traffic.dump (.device ref)))
  have gs (fd : Nat) := native _ (frame_world h _ (getNlSock_sameWGWorld fd))
  have ss (fd : Nat) (sock : NlSock) := native _ (frame_tag h _ ((setNlSock_sameDump fd sock).of_factor
    (fun s : WGStoreView => fun pid => (s.dev.bind fun d => d.peers[pid]?).map Peer.handshakeState)
    handshakeTagAt (fun _ => rfl)))
  have ds (fd : Nat) (ref : DeviceRef) : Framing.Preserves (ProductInv h) (monadLift (netlinkDumpStart fd ref) : Leanux.M Unit) := native _ (frame h _ (traffic.dump (.start fd ref)))
  have dr (fd : Nat) : Framing.Preserves (ProductInv h) (monadLift (netlinkRecvmsg fd) : Leanux.M (Option (List NlMessage))) := native _ (frame h _ (traffic.dump (.receive fd)))
  have advance (ticks : Nat) := product_stable _ (advance_sameKernel ticks) h
  cases call <;> simp only [DispatchRetained] at retained
  all_goals try contradiction
  case wgSetMtu n => exact native_socket _ _ h (carrier_env_mtu n h)
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

end Leanux.Proofs.WG.HandshakeSecurity.Exchange.DispatchFrames
