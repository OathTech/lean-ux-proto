import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueControls

/-! The retained native syscall arms preserve physical handshake inputs.
Ingress and worker execution are handled by their checked source contracts. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Control
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Leanux.Proofs.WG.NetlinkDump Queues
set_option maxHeartbeats 600000

private theorem dump_get (ref : DeviceRef) : SameView productView (Leanux.dispatch (.wgGet ref)) := by
  unfold Leanux.dispatch
  apply netlink
  handshake_control_source [modifyAmbient] using [] with [dump_device_cell]

private theorem dump_start (ref : DeviceRef) : SameView productView (Leanux.dispatch (.wgGetStart ref)) := by
  unfold Leanux.dispatch
  apply socket
  have get := fun fd => (show SameView view (getNlSock fd) from (getNlSock_sameWGWorld fd).factor view)
  have set := fun fd sock => dump_cell (setNlSock_sameDump fd sock)
  handshake_control_source [skipCut,skipCutExactly] using [] with [get,set,dump_start_cell]

private theorem dump_receive : SameView productView (Leanux.dispatch .wgGetRecv) := by
  unfold Leanux.dispatch
  apply socket
  handshake_control_source [skipCut,unsupported,modifyAmbient] using [] with [dump_receive_cell]

private theorem advance (ticks : Nat) : SameView productView (Leanux.dispatch (.wgAdvance ticks)) := by
  unfold Leanux.dispatch
  apply SameView.bind (fs (fdget KCOV_FD))
  intro f
  have tail : SameView productView (do
      let ret ← Env.advance ticks
      liftM (fdput f)
      pure ret : Leanux.M Int) :=
    (store (advance_sameKernel ticks)).bind fun ret=>(fs (fdput f)).bind fun _=>SameView.pure _ ret
  dsimp only
  split
  · apply SameView.bind
    · intro initial
      exact productAmbient_spec (unsupported _ : AmbientM Unit) _ (fun _ _ h=>h)
    · intro _; exact tail
  · exact tail

/-- The exact retained dispatch subset frames handshake messages without a
validity premise; up/down callbacks may change other device state. -/
theorem retained (call : Syscall) (kept : DispatchRetained call) :
    SameView productView (Leanux.dispatch call) := by
  cases call with
  | eventfd2 count flags=>exact fs _
  | dup fd=>exact fs _
  | dup3 oldfd newfd flags=>exact fs _
  | close fd=>exact fs _
  | read fd count=>exact fs _
  | write fd count buf=>exact fs _
  | pipe2 flags=>exact fs _
  | fcntl fd cmd arg=>exact fs _
  | epollCreate1 flags=>exact fs _
  | epollCtl epfd op fd events data=>exact fs _
  | epollWait epfd maxevents timeout=>exact fs _
  | wgGet ref=>exact dump_get ref
  | wgGetStart ref=>exact dump_start ref
  | wgGetRecv=>exact dump_receive
  | wgUp=>exact socket _ _ up
  | wgSetMtu n=>exact socket _ _ (mtu n)
  | wgDeladdr family=>exact rtnetlink _ (store (wgDeladdr_sameKernel family))
  | wgDelroute family named dst plen oif typeCode metric=>exact rtnetlink _ (delroute family named dst plen oif typeCode metric)
  | wgAddroute dst plen oif typeCode metric mtu flags=>exact rtnetlink _ (addroute dst plen oif typeCode metric mtu flags)
  | wgAddaddr addr plen=>exact rtnetlink _ (addaddr addr plen)
  | wgAdvance ticks=>exact advance ticks
  | wgDown=>exact socket _ _ down
  | wgNetnsClose=>
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w result v run
    exact congrArg (fun s : WGStoreView=>s.dev.map (·.handshakeQueue))
      ((ProjectedAction.iff_run _ _ _).mp SyscallFrames.netnsClose_sameWGStore w result v run)
  | seccompInstall via flags filter len bad mode=>exact seccomp _
  | seccompProbe nr args target strict=>cases target <;> exact seccomp _
  | seccompPrctl cmd args=>exact seccomp _
  | seccompCapdrop=>exact seccomp _
  | seccompQuery cmd action flags=>exact seccomp _
  | _=>exact kept.elim

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Control
