import Leanux.Proofs.WG.RetirementSecurity.OccurrenceNonpollJournal

/-! The same shared-journal encryption iteration certifies its actual poll
entry, keeps the detached alias across softirq, and consumes it in its native
tail. Source Stop retains all certificates already emitted. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open OccurrenceStack TransmitSecurity

theorem encryption_tail (item : Option (List SkbId)) :
    PrefixEnsures (Inv item.toList) Safe (Driver.encryptTailObserved Journal.hooks item)
      (fun _ => Inv []) := by
  have history : Driver.ProductHistorySafe Safe (Driver.encryptTailObserved Journal.hooks item) :=
    (show Driver.encryptTailObserved nonpollHooks item = Driver.encryptTailObserved Journal.hooks item from rfl) ▸
      Driver.encryptTail_history hooks_safe.actors item
  intro w h before
  obtain ⟨suffix,extension,safe,normal⟩ := history w h before.2
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix (Driver.encryptTailObserved Journal.hooks item) w h).1 with
  | error stop => trivial
  | ok output =>
    obtain ⟨value,v⟩ := output
    have projected := Driver.encryptTail_projects Journal.hooks_projects item
    rw [Driver.nonce_encryptTailObserved_eq] at projected
    have erases : ErasesPrefix (Nonce.encryptTailObserved item) (RxWorkers.encryptTailSource item) :=
      workerIterPrefix_erases _ _ (erasesPrefix_lift _) (Nonce.reschedObserved_erases _ _)
    have native := DriverOwnership.product_native projected erases
      w v h result
    exact ⟨OccurrenceEncrypt.tail (by simpa only [List.append_nil] using before.1) native,safe⟩

theorem encryption_iteration :
    PrefixPreserves (Inv []) Safe (Driver.encryptIterObserved Journal.hooks) := by
  unfold Driver.encryptIterObserved
  change PrefixEnsures (Inv []) Safe (Journal.poll >>= _) (fun _ => Inv [])
  apply PrefixEnsures.bind poll
  intro item
  apply PrefixEnsures.bind (softirq (active := item.toList))
  intro _
  exact encryption_tail item

end Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
