import Leanux.Proofs.WG.Queues.HolderScheduler
import Leanux.Proofs.WG.Queues.DeferredPreservation

/-! The actual crypt-worker wait retains its committed RX-removal suffix.
The final deliverSent action changes no holder or physical-ring observation. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderDeferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders HolderScheduler

/-- Only the original receive-worker account is left to its concrete caller. -/
theorem runCryptWorkers_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event)
    (receive : PrefixPreserves (Inv initial loans before) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration) :
    PrefixPreserves (Inv initial loans before) (fun _ => True) RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves (I := Inv initial loans before)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => HolderScheduler.store hi same) _
    (HolderScheduler.schedule_preserves initial loans before receive none)

/-- The exact original observer supplies the removed-packet suffix for this
normal run, including all real crypt/NET_RX work before delivery. -/
theorem runCryptWorkers_normal (h : List RxHistory.Event)
    (receive : PrefixPreserves (Inv cs loans h) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration)
    (funded : Boundary cs loans w.wg) (physical : DecryptIteration.Physical w)
    (run : Env.runCryptWorkers.run w = .ok ((),v)) :
    (∃ suffix, (runPrefix RxHistory.runCryptWorkers w h).2 = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧
      DecryptIteration.Physical v := by
  have actual := (RxHistory.runCryptWorkers_erases w h).trans run
  have post := (runCryptWorkers_preserves cs loans h receive w h
    ⟨HolderNapi.at_start funded h,physical⟩).choose_spec.2.2
  simpa only [actual,HolderScheduler.Inv,HolderNapi.At] using post

end Leanux.Proofs.WG.Queues.RxCredits.HolderDeferred
