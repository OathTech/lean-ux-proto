import Leanux.Proofs.WG.Roaming.PollAuthenticationTrafficSource
import Leanux.Proofs.WG.Roaming.RemoteOuterRulesSource
import Leanux.Proofs.WG.Packets.PublicationSyscalls
import Leanux.Proofs.WG.Lifetimes.DispatchSource
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication.Syscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes Configuration

/-- Local invariant-generalized variant of the original socket wrapper rule. -/
theorem socketCallOn_preserves_variant (fd : Nat) (body : RxHistory.Obs Int)
    (bodyChecked : PrefixPreserves Reached PublicSafe body) :
    PrefixPreserves Reached PublicSafe (RxHistory.socketCallOn fd body) :=
  RemoteOuterRules.socket _ _ reached_safe
    (fun {_} action => quiet_lift _ (PublicationOuter.lift_fs action))
    fd body bodyChecked

theorem retained (call : Syscall) (selected : DispatchRetained call) :
    PrefixPreserves Reached PublicSafe (RxHistory.syscallDispatch call) := by
  have original := PublicationSyscalls.dispatch call
  cases call
  all_goals simp only [DispatchRetained] at selected
  all_goals first
    | contradiction
    | exact audit _ original

theorem observed : PrefixPreserves Reached PublicSafe (RxHistory.syscallDispatch .wgObserve) := by
  change PrefixPreserves Reached PublicSafe (do
    let (ret, observed) ← RxHistory.observe
    liftPrefix (modifyAmbient fun w => {w with extraOut :=
      (["datagrams","replies","stats"].map fun k => (k,observed.getObjValD k))})
    RxHistory.socketCallOn LISTEN4_FD (pure ret))
  apply PrefixPreserves.bind Traffic.observe
  rintro ⟨ret,observed⟩
  dsimp only
  apply PrefixPreserves.bind
  · exact quiet_lift _ (PublicationOuter.lift_modify _ (fun _ => rfl))
  intro _
  exact socketCallOn_preserves_variant LISTEN4_FD _ (PrefixPreserves.pure reached_safe ret)

theorem dispatch (call : Syscall) :
    PrefixPreserves Reached PublicSafe (RxHistory.syscallDispatch call) := by
  rw [rxDispatch_source]
  apply dispatchWith_preserves
  · exact retained
  · intro attrs
    exact audit _ (PublicationSyscalls.dispatchSet attrs)
  · exact audit _ PublicationSyscalls.dispatchCreate
  · exact audit _ PublicationSyscalls.dispatchDelete
  · intro family addr payload opts
    exact audit _ (PublicationSyscalls.dispatch (.wgXmit family addr payload opts))
  · intro family port msg tos ll dest
    exact socketCallOn_preserves_variant SENDER_FD _ (Traffic.inject family port msg tos ll dest)
  · exact Traffic.flood
  · exact Traffic.batch
  · exact observed

theorem syscall (call : Syscall) :
    PrefixPreserves Reached PublicSafe (RxHistory.syscall call) := by
  rw [syscallRx_factor]
  exact SyscallSource.preserves reached_safe reached_wgStore call _ _ _ _ _ _ _
    (dispatch call) Deferred.send Deferred.idle
    (audit _ PublicationRemaining.route) Deferred.afterXmit Deferred.afterAdvance
    (audit _ PublicationControls.netnsCleanup)

end Leanux.Proofs.WG.Roaming.PollAuthentication.Syscalls
