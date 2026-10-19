import Leanux.Proofs.WG.Queues.HandshakeWorker
import Leanux.Proofs.WG.Queues.HolderInitial
import Leanux.Proofs.WG.Queues.HolderSendEnvironment
import Leanux.Proofs.WG.Origins.OwnerDeferred

/-! The actual crypt wait and completion guard retain the stronger auxiliary
account without a receive callback premise. Completion emptiness is derived
from the caller's actual decrypt-ring flag and the same native guard run. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderAuxDeferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

theorem crypt (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves (I:=HolderAuxiliary.Inv initial loans before)
    (fun _ _ hi => hi.2.1.safe) (fun _ _ _ same hi => HolderAuxiliary.store hi same) _
    (HandshakeWorker.schedule initial loans before none)

theorem drained (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (what : String) (flags : List Bool) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (requireDrainedPrefix what flags)) := by
  apply HolderAuxiliary.pair
  · exact HolderDeferred.drained_preserves initial loans before what flags
  · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.drained) what flags
  · intro w h hi x v run
    cases x
    have actual := (RxHistory.mixed_erases (requireDrainedPrefix_erases what flags) w h).symm.trans run
    exact (requireDrained_normal what flags w v actual).1 ▸ hi.2.2

/-- The original crypt-wait run determines the fresh removal journal. Its
normal endpoint retains the complete auxiliary account at that same cut. -/
theorem crypt_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : Env.runCryptWorkers.run w=.ok ((),v)) :
    HolderAuxiliary.Inv initial loans before (runPrefix RxHistory.runCryptWorkers w h).2 v := by
  have actual := (RxHistory.runCryptWorkers_erases w h).trans run
  have post := (crypt initial loans before w h hi).choose_spec.2.2
  simpa only [actual] using post

/-- A successful completion guard discharges the current remaining ledger,
provided its actual flags contain the decrypt-ring test. -/
theorem drained_empty (hi : HolderAuxiliary.Inv initial loans before h w)
    (ringFlag : ∀ d, w.wg.dev=some d → (!d.decryptQueue.empty)∈flags)
    (run : runPrefix (RxHistory.mixed (requireDrainedPrefix what flags)) w h=(.ok ((),v),k)) :
    ∃ prior, h=before++prior ∧ remaining initial (NapiCarrier.removedPackets prior)=[] ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket), v.wg.dev=some d → d.rxSkbs[id]?≠some packet) ∧
      HolderAuxiliary.Inv initial loans before k v := by
  have actual := (RxHistory.mixed_erases (requireDrainedPrefix_erases what flags) w h).symm.trans
    (congrArg Prod.fst run)
  obtain ⟨prior,history,holders,funded,stable⟩ := hi.1.1
  obtain ⟨epoch,n,ringHistory,physical⟩ := hi.1.2
  have empty := requireDrained_empty what flags w v _ _ funded.carriers stable physical ringFlag actual
  have post := (drained initial loans before what flags w h hi).choose_spec.2.2
  rw [run] at post
  exact ⟨prior,history,empty.1,empty.2,post⟩

end Leanux.Proofs.WG.Queues.RxCredits.HolderAuxDeferred
