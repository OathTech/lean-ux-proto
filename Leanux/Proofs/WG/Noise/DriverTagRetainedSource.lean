import Leanux.Proofs.WG.Noise.DriverTagSyscallFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Syscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Leanux.Proofs.WG.Configuration

macro "syscall_quiet_step " entry:term : tactic => `(tactic| first
  | rw [lift_bind]
  | rw [lift_pure]
  | (current_env_at liftM; unfold liftM)
  | (current_env_at MonadLiftT.monadLift; unfold MonadLiftT.monadLift)
  | (current_env_at MonadLift.monadLift; unfold MonadLift.monadLift)
  | (current_env_at wgGetDevice; exact dump_lift $entry (.device _))
  | (current_env_at netlinkDumpStart; exact dump_lift $entry (.start _ _))
  | (current_env_at netlinkRecvmsg; exact dump_lift $entry (.receive _))
  | (current_env_at getNlSock; exact dump_frame $entry _ ((getNlSock_sameWGWorld _).factor dumpView))
  | (current_env_at setNlSock; exact dump_frame $entry _ (setNlSock_sameDump _ _))
  | (current_env_at setMtu; exact scalar_lift $entry _)
  | (current_env_at socketCallOnWith; apply Outer.socketCallOn_tag_variant $entry)
  | (current_env_at netlinkRequestWith; apply Outer.netlinkRequest_tag_variant $entry)
  | rw [lift_bind]
  | rw [lift_pure]
  | driver_outer_step $entry
  | split)

theorem dump_dispatch (entry : TagMap) (device : DeviceRef) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (Leanux.dispatch (.wgGet device))) := by
  simp only [Leanux.dispatch,netlink_lift]
  repeat' syscall_quiet_step entry
  all_goals exact dump_lift entry (.device device)

theorem dump_start (entry : TagMap) (device : DeviceRef) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (Leanux.dispatch (.wgGetStart device))) := by
  simp only [Leanux.dispatch,socket_lift]
  repeat' syscall_quiet_step entry
  all_goals exact dump_lift entry (.start DUMP_FD device)

theorem dump_receive (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (Leanux.dispatch .wgGetRecv)) := by
  simp only [Leanux.dispatch,socket_lift]
  repeat' syscall_quiet_step entry
  all_goals exact dump_lift entry (.receive DUMP_FD)

theorem advance (entry : TagMap) (ticks : Nat) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (Leanux.dispatch (.wgAdvance ticks))) := by
  simp only [Leanux.dispatch]
  repeat' first
    | (current_env_at Env.advance; exact lift_product_store entry _ (advance_sameKernel _))
    | syscall_quiet_step entry

def retained : Syscall → ProductObs Int
  | .wgUp => socketCallOnWith (fun {_} a => liftPrefix a) SENDER_FD Environment.upObserved
  | .wgDown => socketCallOnWith (fun {_} a => liftPrefix a) SENDER_FD Environment.downObserved
  | .wgDeladdr family => rtnetlinkRequestWith (fun {_} a => liftPrefix a) (liftPrefix (Env.wgDeladdr family))
  | .wgDelroute family named dst plen oif typeCode metric =>
      rtnetlinkRequestWith (fun {_} a => liftPrefix a)
        (liftPrefix (Env.wgDelroute family named dst plen oif typeCode metric))
  | .wgAddroute dst plen oif typeCode metric mtu nlflags =>
      rtnetlinkRequestWith (fun {_} a => liftPrefix a)
        (liftPrefix (Env.wgAddroute dst plen oif typeCode metric mtu nlflags))
  | .wgAddaddr addr plen => rtnetlinkRequestWith (fun {_} a => liftPrefix a)
      (liftPrefix (Env.wgAddaddr addr plen))
  | call => liftPrefix (Leanux.dispatch call)

theorem retained_preserves (entry : TagMap) (call : Syscall) (selected : DispatchRetained call) :
    PrefixPreserves (StateInv entry) ValidHistory (retained call) := by
  cases call
  case wgGet device => exact dump_dispatch entry device
  case wgGetStart device => exact dump_start entry device
  case wgGetRecv => exact dump_receive entry
  case wgUp =>
    exact Outer.socketCallOn_tag_variant entry _ _ (Environment.upObserved_preserves entry)
  case wgDown =>
    exact Outer.socketCallOn_tag_variant entry _ _ (Environment.downObserved_preserves entry)
  case wgSetMtu mtu =>
    change PrefixPreserves _ _ (liftPrefix (Leanux.socketCallOn SENDER_FD (Env.setMtu mtu)))
    rw [socket_lift]
    exact Outer.socketCallOn_tag_variant entry _ _ (scalar_lift entry mtu)
  case wgDeladdr family =>
    exact Outer.rtnetlinkRequest_tag_variant entry _ (lift_product_store entry _ (wgDeladdr_sameKernel family))
  case wgDelroute family named dst plen oif typeCode metric =>
    apply Outer.rtnetlinkRequest_tag_variant entry
    apply lift_product_frame
    apply SameView.of_factor (view := fun w : World => wgStoreView w.wg) _
      (fun s => responseTagMap s.dev) (fun w => tagView w.wg) (fun _ => rfl)
    unfold Env.wgDelroute
    syscall_routing_store
  case wgAddroute dst plen oif typeCode metric mtu nlflags =>
    apply Outer.rtnetlinkRequest_tag_variant entry
    apply lift_product_frame
    apply SameView.of_factor (view := fun w : World => wgStoreView w.wg) _
      (fun s => responseTagMap s.dev) (fun w => tagView w.wg) (fun _ => rfl)
    unfold Env.wgAddroute
    syscall_routing_store
  case wgAddaddr addr plen =>
    apply Outer.rtnetlinkRequest_tag_variant entry
    apply lift_product_frame
    apply SameView.of_factor (view := fun w : World => wgStoreView w.wg) _
      (fun s => responseTagMap s.dev) (fun w => tagView w.wg) (fun _ => rfl)
    unfold Env.wgAddaddr
    syscall_routing_store
  case wgAdvance ticks => exact advance entry ticks
  case wgNetnsClose =>
    exact lift_product_frame entry _ (SyscallFrames.netnsClose_sameWGStore.of_factor
      (fun s => responseTagMap s.dev) (fun w => tagView w.wg) (fun _ => rfl))
  case seccompProbe nr args target strict => cases target <;> exact Outer.lift_seccomp entry _
  all_goals try (solve | cases selected)
  all_goals simp only [retained,Leanux.dispatch]
  all_goals first
    | (current_env_at liftFS; exact Outer.lift_fs entry _)
    | (current_env_at liftSeccomp; exact Outer.lift_seccomp entry _)

theorem retained_erases (call : Syscall) : ErasesPrefix (retained call) (Leanux.dispatch call) := by
  cases call
  case wgUp => exact Outer.socketCallOn_erases _ _ _ Environment.upObserved_erases
  case wgDown => exact Outer.socketCallOn_erases _ _ _ Environment.downObserved_erases
  case wgDeladdr family => exact Outer.rtnetlinkRequest_erases _ _ (erasesPrefix_lift _)
  case wgDelroute family named dst plen oif typeCode metric =>
    exact Outer.rtnetlinkRequest_erases _ _ (erasesPrefix_lift _)
  case wgAddroute dst plen oif typeCode metric mtu nlflags =>
    exact Outer.rtnetlinkRequest_erases _ _ (erasesPrefix_lift _)
  case wgAddaddr addr plen => exact Outer.rtnetlinkRequest_erases _ _ (erasesPrefix_lift _)
  all_goals exact erasesPrefix_lift _


end Leanux.Proofs.WG.Noise.DriverTags.Syscalls
