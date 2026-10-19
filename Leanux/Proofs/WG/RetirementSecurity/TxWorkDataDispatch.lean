import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionDump

/-! Concrete traffic, observation and full/stepped dump dispatch handlers
retain TX service. Descriptor borrowing, cutoff records and cursor effects are
composed at their real source positions. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem dump_socket_get_actor (fd : Nat) :
    Preserves (At (Covered [] []) [] active) (liftWG (getNlSock fd)) :=
  At.native (fun _=>serving_store ((getNlSock_sameWGWorld fd).factor wgStoreView))
    (TxSuspension.dump_socket_get fd)

theorem dump_socket_set_actor (fd : Nat) (sock : NlSock) :
    Preserves (At (Covered [] []) [] active) (liftWG (setNlSock fd sock)) :=
  At.native (fun _=>serving_dump_frame (setNlSock_sameDump fd sock)) (TxSuspension.dump_socket_set fd sock)

theorem exact_cut_actor (site : HiddenSite) (count : Nat) (between : List HiddenSite) :
    Preserves (At P crypt active) (skipCutExactly site count between : Leanux.M Unit) :=
  actor_ambient (TxSuspension.exact_cut_ambient site count between)

macro "actor_dump_step" : tactic => `(tactic| first
  | (rx_retention_head socketCallOn; apply socket_actor)
  | (rx_retention_head netlinkRequest; apply netlink_actor)
  | (rx_retention_head skipCutExactly; exact exact_cut_actor _ _ _)
  | (tx_actor_source wgGetDevice; exact dump_device_actor _)
  | (tx_actor_source netlinkDumpStart; exact dump_start_actor _ _)
  | (tx_actor_source netlinkRecvmsg; exact dump_recv_actor _)
  | (tx_actor_source getNlSock; exact dump_socket_get_actor _)
  | (tx_actor_source setNlSock; exact dump_socket_set_actor _ _)
  | actor_traffic_step)

theorem dispatch_dump_actor (ref : DeviceRef) :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgGet ref)) := by
  simp only [dispatch]
  repeat' actor_dump_step

theorem dispatch_dump_start_actor (ref : DeviceRef) :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgGetStart ref)) := by
  simp only [dispatch]
  repeat' actor_dump_step

theorem dispatch_dump_recv_actor :
    Preserves (At (Covered [] []) [] active) (dispatch .wgGetRecv) := by
  simp only [dispatch]
  repeat' actor_dump_step

theorem dispatch_transmit_actor (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Preserves (At (Covered locals crypt) crypt active) (dispatch (.wgXmit family addr payload opts)) := by
  simp only [dispatch]
  apply socket_actor
  repeat' actor_traffic_step

theorem dispatch_inject_actor (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves (At (Covered locals crypt) crypt []) (dispatch (.wgInject family port msg tos ll dest)) :=
  socket_actor _ _ (inject_actor family port msg tos ll dest)

theorem dispatch_flood_actor (count port family : Nat) (messages : List (List UInt8)) :
    Preserves (At (Covered locals crypt) crypt []) (dispatch (.wgFlood count port family messages)) :=
  flood_actor count port family messages

theorem dispatch_batch_actor (items : List Env.BatchItem) (waitMs : Nat) :
    Preserves (At (Covered locals crypt) crypt []) (dispatch (.wgBatch items waitMs)) := batch_actor items

theorem dispatch_observe_actor : Preserves (At (Covered locals crypt) crypt []) (dispatch .wgObserve) := by
  simp only [dispatch]
  repeat' first
    | (rx_retention_head Env.observe; exact observe_actor)
    | (rx_retention_head socketCallOn; apply socket_actor)
    | actor_traffic_step

theorem dispatch_advance_actor (ticks : Nat) :
    Preserves (At (Covered locals crypt) crypt active) (dispatch (.wgAdvance ticks)) := by
  simp only [dispatch]
  repeat' first
    | (rx_retention_head Env.advance; exact advance_actor _)
    | (tx_file_lift FS.M
       first
       | env_operation_fact TxSuspension.Nested.fd_get
       | env_operation_fact TxSuspension.Nested.fd_put)
    | actor_traffic_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
