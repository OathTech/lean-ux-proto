import Leanux.Proofs.WG.Index.DumpCoreFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DumpCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits Queues.RxCredits.DurableHolders

theorem native_join (action : NetlinkDumpCall)
    (cs : Ledger) (loans : Reservations)
    (w v : WGWorld) (a b : Ambient) (result : action.Result)
    (pre : ConfigurationIndex.Entry cs loans w)
    (run : ((action.original.run w).run a)=.ok ((result,v),b))
    (funded : ∀holders : DurableHolders,holders.Funded cs loans w → StableRx cs w →
      ∃afterHolders : DurableHolders,afterHolders.Funded cs loans v ∧ StableRx cs v ∧ afterHolders.base=holders.base) :
    ConfigurationIndex.Entry cs loans v := by
  obtain ⟨holders,paid,stable⟩ := pre.1.1
  obtain ⟨afterHolders,paidAfter,stableAfter,sameBase⟩ := funded holders paid stable
  have rich := (hoare_iff_run_ambient _ _ _).mp (call_frame action w.dev)
    w a result v b (StagingRich.refl {dev:=w.dev}) run
  have shape := (hoare_iff_run_ambient _ _ _).mp (call_shape action w.dev.isSome)
    w a result v b ⟨rfl,fun d hd=>handshake_of_core d (pre.2.2 d hd)⟩ run
  have extra := (hoare_iff_run_ambient _ _ _).mp (call_essentials action)
    w a result v b ⟨pre.1.2.1,pre.1.2.2,pre.2.1⟩ run
  exact ⟨⟨⟨afterHolders,paidAfter,stableAfter⟩,extra.1,extra.2.1⟩,extra.2.2,
    core_of_funded w v holders afterHolders cs loans pre.1.2.2 pre.1.2.1
      paid paidAfter sameBase rich shape pre.2.2⟩

theorem socket_entry (cs : Ledger) (loans : Reservations) (fd : Nat) :
    Hoare (netlinkDump fd)
      (fun w=>ConfigurationIndex.Entry cs loans w ∧ (socketAt fd w).cbRunning=true)
      (fun _=>ConfigurationIndex.Entry cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases result
  apply native_join (.dump fd) cs loans w v a b () pre.1 run
  intro holders paid stable
  obtain ⟨next,after,stableAfter⟩ := netlinkDump_funded fd paid stable pre.2 a b run
  exact ⟨holders.withCursor fd next,after,stableAfter,by unfold withCursor;split <;>rfl⟩

theorem start_entry (cs : Ledger) (loans : Reservations) (fd : Nat) (ref : DeviceRef) :
    Preserves (ConfigurationIndex.Entry cs loans) (netlinkDumpStart fd ref) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases result
  apply native_join (.start fd ref) cs loans w v a b () pre run
  intro holders paid stable
  obtain ⟨next,after,stableAfter⟩ := netlinkDumpStart_funded fd ref paid stable a b run
  exact ⟨holders.withCursor fd next,after,stableAfter,by unfold withCursor;split <;>rfl⟩

theorem receive_entry (cs : Ledger) (loans : Reservations) (fd : Nat) :
    Preserves (ConfigurationIndex.Entry cs loans) (netlinkRecvmsg fd) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  apply native_join (.receive fd) cs loans w v a b result pre run
  intro holders paid stable
  obtain ⟨next,after,stableAfter⟩ := netlinkRecvmsg_funded fd paid stable a b run
  exact ⟨holders.withCursor fd next,after,stableAfter,by unfold withCursor;split <;>rfl⟩

theorem device_entry (cs : Ledger) (loans : Reservations) (ref : DeviceRef) :
    Preserves (ConfigurationIndex.Entry cs loans) (wgGetDevice ref) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  apply native_join (.device ref) cs loans w v a b result pre run
  intro holders paid stable
  obtain ⟨next,after,stableAfter⟩ := wgGetDevice_funded ref paid stable a b run
  exact ⟨holders.withCursor 7 next,after,stableAfter,by unfold withCursor;split <;>rfl⟩

end Leanux.Proofs.WG.Index.DumpCore
