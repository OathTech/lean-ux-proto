import Leanux.Proofs.WG.TransmitSecurity.EmissionControlFrames
import Leanux.Proofs.WG.TransmitSecurity.EmissionCleanupFrames

/-! The complete quiet syscall dispatcher retains pending emissions. Up/down,
packet traffic and worker callbacks use their observed source paths instead. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EmissionDispatch
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues AuthenticatedEffects EmissionOuter

set_option maxHeartbeats 600000 in
theorem quiet (call : Syscall) (retained : DispatchRetained call)
    (notUp : call ≠ .wgUp) (notDown : call ≠ .wgDown) :
    SameView Sent (Leanux.dispatch call) := by
  cases call <;> simp only [DispatchRetained] at retained
  all_goals try contradiction
  case wgSetMtu n => exact socket _ _ (EmissionControl.mtu n)
  case wgDeladdr family => exact rtnetlink _ (EmissionControl.del_addr family)
  case wgDelroute family named dst plen oif typeCode metric =>
    exact rtnetlink _ (EmissionControl.del_route family named dst plen oif typeCode metric)
  case wgAddroute dst plen oif typeCode metric mtu nlflags =>
    exact rtnetlink _ (EmissionControl.add_route dst plen oif typeCode metric mtu nlflags)
  case wgAddaddr addr plen => exact rtnetlink _ (EmissionControl.add_addr addr plen)
  case wgNetnsClose => exact EmissionControl.netns_close
  case wgGet ref =>
    apply netlink
    intro initial
    change Preserves (fun w : World => Sent w = initial) _
    have gd : Preserves (fun w : World => Sent w = initial)
        (monadLift (wgGetDevice ref) : Leanux.M (Except Int Lean.Json)) :=
      wg _ (EmissionDump.device ref) initial
    have effects {α : Type} (a : AmbientM α) : Preserves (fun w : World => Sent w = initial)
        (monadLift a : Leanux.M α) := ambient a initial
    routing_tx_source [modifyAmbient] using [gd,effects]
    all_goals exact edit _ (fun _ => rfl) initial
  case wgGetStart ref =>
    apply socket
    intro initial
    change Preserves (fun w : World => Sent w = initial) _
    have getSock (fd : Nat) : Preserves (fun w : World => Sent w = initial)
        (monadLift (getNlSock fd) : Leanux.M NlSock) :=
      wg _ ((getNlSock_sameWGWorld fd).factor WGWorld.sent) initial
    have setSock (fd : Nat) (sock : NlSock) : Preserves (fun w : World => Sent w = initial)
        (monadLift (setNlSock fd sock) : Leanux.M Unit) :=
      wg _ (fun state => EmissionDump.set_sock (· = state) fd sock) initial
    have start (fd : Nat) (ref : DeviceRef) : Preserves (fun w : World => Sent w = initial)
        (monadLift (netlinkDumpStart fd ref) : Leanux.M Unit) :=
      wg _ (EmissionDump.start fd ref) initial
    have effects {α : Type} (a : AmbientM α) : Preserves (fun w : World => Sent w = initial)
        (monadLift a : Leanux.M α) := ambient a initial
    routing_tx_source [skipCut,skipCutExactly] using [getSock,setSock,start,effects]
  case wgGetRecv =>
    apply socket
    intro initial
    change Preserves (fun w : World => Sent w = initial) _
    have receive (fd : Nat) : Preserves (fun w : World => Sent w = initial)
        (monadLift (netlinkRecvmsg fd) : Leanux.M (Option (List NlMessage))) :=
      wg _ (EmissionDump.receive fd) initial
    have effects {α : Type} (a : AmbientM α) : Preserves (fun w : World => Sent w = initial)
        (monadLift a : Leanux.M α) := ambient a initial
    routing_tx_source [skipCut,unsupported,modifyAmbient] using [receive,effects]
    all_goals exact edit _ (fun _ => rfl) initial
  case wgAdvance ticks =>
    intro initial
    change Preserves (fun w : World => Sent w = initial) _
    have files {α : Type} (a : FS.M α) : Preserves (fun w : World => Sent w = initial)
        (monadLift a : Leanux.M α) := fs a initial
    have advanced : Preserves (fun w : World => Sent w = initial) (Env.advance ticks) :=
      EmissionControl.advance ticks initial
    have effects {α : Type} (a : AmbientM α) : Preserves (fun w : World => Sent w = initial)
        (monadLift a : Leanux.M α) := ambient a initial
    dsimp only [Leanux.dispatch]
    routing_tx_source [unsupported] using [files,advanced,effects]
  case seccompProbe nr args target strict => cases target <;> exact seccomp _
  case seccompInstall => exact seccomp _
  case seccompPrctl => exact seccomp _
  case seccompCapdrop => exact seccomp _
  case seccompQuery => exact seccomp _
  all_goals exact fs _

end Leanux.Proofs.WG.TransmitSecurity.EmissionDispatch
