import Leanux.Proofs.WG.RetirementSecurity.TxWorkOrdinary

/-! Every original syscall preserves TX service from an actual idle runner
boundary. Native network callbacks are discharged, and ordinary file/seccomp
calls use their exact WG-store frame rather than a suspension assumption. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem network_dispatch_actor (call : Syscall) (network : ¬Ordinary call) :
    Preserves (At (Covered [] []) [] []) (dispatch call) := by
  cases call with
  | wgSet attrs=>exact dispatch_configure_actor attrs
  | wgGet ref=>exact dispatch_dump_actor ref
  | wgGetStart ref=>exact dispatch_dump_start_actor ref
  | wgGetRecv=>exact dispatch_dump_recv_actor
  | wgUp=>exact dispatch_up_actor
  | wgXmit family addr payload opts=>exact dispatch_transmit_actor family addr payload opts
  | wgSetMtu mtu=>exact dispatch_mtu_actor mtu
  | wgInject family port msg tos ll dest=>exact dispatch_inject_actor family port msg tos ll dest
  | wgDeladdr family=>exact dispatch_deladdr_actor family
  | wgDelroute family named dst plen oif kind metric=>exact dispatch_delroute_actor family named dst plen oif kind metric
  | wgAddroute dst plen oif kind metric mtu flags=>exact dispatch_addroute_actor dst plen oif kind metric mtu flags
  | wgAddaddr addr plen=>exact dispatch_addaddr_actor addr plen
  | wgFlood count port family messages=>exact dispatch_flood_actor count port family messages
  | wgBatch items waitMs=>exact dispatch_batch_actor items waitMs
  | wgObserve=>exact dispatch_observe_actor
  | wgAdvance ticks=>exact dispatch_advance_actor ticks
  | wgCreate=>exact dispatch_create_actor
  | wgDown=>exact dispatch_down_actor
  | wgDelete=>exact dispatch_delete_actor
  | wgNetnsClose=>exact dispatch_namespace_actor
  | _=>exact False.elim (network True.intro)

theorem network_number (call : Syscall) (network : ¬Ordinary call) : syscallNr call=none := by
  cases call <;> first | rfl | exact False.elim (network True.intro)

theorem syscall_boundary_actor (call : Syscall)
    (before : At (Covered [] []) [] [] w) (idle : w.ambient.suspended=[])
    (run : (Leanux.syscall call).run w=.ok (result,v)) : At (Covered [] []) [] [] v := by
  classical
  by_cases ordinary : Ordinary call
  · exact ordinary_syscall_actor call ordinary before idle run
  · exact (hoare_iff_run _ _ _).mp
      (syscall_network_actor call (network_number call ordinary) (network_dispatch_actor call ordinary))
      w result v before run

end Leanux.Proofs.WG.RetirementSecurity.TxWork
