import Leanux.Proofs.WG.Index.ReceiverCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

namespace Reached
theorem receiveStep_account (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      Origins.HistoryAdapters.receiveStep := by
  intro w h pre
  obtain ⟨suffix,history,safe,post⟩ := HandshakeSlotHistory.receiveStep w h ⟨pre.2.1,pre.2.2⟩
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix Origins.HistoryAdapters.receiveStep w h).1 with
  | error stop => trivial
  | ok pair =>
    rw [run] at post
    exact ⟨HandshakeWorker.step_normal pre (Prod.ext run rfl),post⟩

theorem receiveStep_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (Aux initial loans before) OwnerChecks.Safe
      Origins.HistoryAdapters.receiveStep := by
  apply aux_pair _ initial loans before (receiveStep_account initial loans before)
  intro w h pre result v run
  have native := DecryptIteration.native_normal Origins.HistoryAdapters.receiveStep_erases
    (Prod.ext run rfl)
  obtain ⟨suffix,_,cut⟩ := Incoming.cut_of_aux pre
  have post := Incoming.receiveStep_cut (remaining initial (NapiCarrier.removedPackets suffix))
    loans w.wg w.ambient result v.wg v.ambient cut native
  exact ⟨post.2.2.1,post.2.2.2⟩

theorem receiveIteration_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (Aux initial loans before) OwnerChecks.Safe
      Origins.HistoryAdapters.receiveIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ pre => pre.1.2.1.safe)
    (receiveStep_preserves initial loans before)
  apply viewLiftPrefix_preserves productStoreView (fun _ _ pre => pre.1.2.1.safe) _
    (condResched_sameKernel .receiveWorker)
  intro h w v same pre
  exact aux_store same pre

end Reached

end Leanux.Proofs.WG.Index
