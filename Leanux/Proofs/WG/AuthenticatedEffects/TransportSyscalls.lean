import Leanux.Proofs.WG.AuthenticatedEffects.TransportRemaining
import Leanux.Proofs.WG.Packets.PublicationSyscalls

/-! Actual dispatcher closure for the earlier replay-entry certificates.
Non-poll audit paths reuse their original state contracts; poll-bearing source
arms use the composed transport observers and preserve every stopped prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportSyscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration TransportOuter
set_option maxHeartbeats 2000000

/-- All actual source arms, including both seccomp probe targets. -/
theorem dispatch (call : Syscall) : TransportChecks.Preserves (RxHistory.syscallDispatch call) := by
  have original := PublicationSyscalls.dispatch call
  cases call with
  | wgInject family port message tos ll dest =>
    exact TransportOuter.socketCallOn _ _ (TransportTraffic.inject family port message tos ll dest)
  | wgFlood count port family messages => exact TransportTraffic.flood count port family messages
  | wgBatch items _ => exact TransportTraffic.batch items
  | wgObserve =>
    change TransportChecks.Preserves (do
      let (ret, observed) ← RxHistory.observe
      liftPrefix (modifyAmbient fun w => {w with extraOut := ["datagrams","replies","stats"].map fun k => (k,observed.getObjValD k)})
      RxHistory.socketCallOn LISTEN4_FD (pure ret))
    apply TransportRemaining.observe.bind
    rintro ⟨ret,observed⟩
    dsimp only
    apply PrefixPreserves.bind
    · exact lift_modify _ (fun _ => rfl)
    intro _
    exact TransportOuter.socketCallOn LISTEN4_FD (pure ret) (PrefixPreserves.pure (fun _ _ hi => hi.2) ret)
  | seccompProbe nr args target strict =>
    cases target <;> exact TransportChecks.audit _ original
  | _ => exact TransportChecks.audit _ original

/-- Source-designated suffixes run after every normal errno return; an actual
Stop retains only the reached prefix. No arbitrary callback premise remains. -/
theorem syscall (call : Syscall) : TransportChecks.Preserves (RxHistory.syscall call) := by
  rw [syscallRx_factor]
  exact syscallWith_preserves call _ _ _ _ _ _ _ (dispatch call)
    TransportDeferred.runSendWorkers TransportDeferred.idleTimers TransportRemaining.route
    TransportDeferred.afterXmit TransportDeferred.afterAdvance TransportControls.netnsCleanup

end Leanux.Proofs.WG.AuthenticatedEffects.TransportSyscalls
