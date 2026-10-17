import Leanux.Proofs.WG.Queues.HandshakeReceiveSlots
import Leanux.Proofs.WG.Queues.DecryptIteration

/-! The original receive observer preserves its owner checks and three-slot
compatibility on the same run. Its incoming history remains arbitrary, and
its original safe Stop suffix is retained without an invented endpoint. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeSlotHistory
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

/-- The actual native receipt is extracted from the original observer erasure. -/
theorem receiveStep : PrefixPreserves
    (fun h w => OwnerChecks.Inv h w ∧ CurrentSlots.Inv w.wg)
    OwnerChecks.Safe Origins.HistoryAdapters.receiveStep := by
  intro w h hi
  obtain ⟨suffix,append,safe,post⟩ := OwnerHandshake.receiveStep w h hi.1
  refine ⟨suffix,append,safe,?_⟩
  cases run : runPrefix Origins.HistoryAdapters.receiveStep w h with
  | mk result k =>
    cases result with
    | error e => trivial
    | ok pair =>
      rcases pair with ⟨x,v⟩
      have owner : OwnerChecks.Inv k v := by simpa only [run] using post
      have native := DecryptIteration.native_normal Origins.HistoryAdapters.receiveStep_erases run
      have entry := (hoare_iff_run_ambient _ _ _).mp HandshakeReceiveSlots.step
        w.wg w.ambient x v.wg v.ambient (HandshakeEntry.of_owner hi.1 hi.2) native
      exact ⟨owner,entry.2⟩

theorem receiveIteration : PrefixPreserves
    (fun h w => OwnerChecks.Inv h w ∧ CurrentSlots.Inv w.wg)
    OwnerChecks.Safe Origins.HistoryAdapters.receiveIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1.safe) receiveStep
  apply viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.1.safe) _
    (condResched_sameKernel .receiveWorker)
  intro h w v same hi
  refine ⟨OwnerWorkers.store h w v same hi.1,?_⟩
  have dev : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  apply CurrentSlots.fields_transport hi.2
  unfold CurrentSlots.fields Leanux.Proofs.WG.Queues.RxCredits.keyWords
  rw [dev]

theorem receiveIteration_normal
    (owner : OwnerChecks.Inv h w) (slots : CurrentSlots.Inv w.wg)
    (run : runPrefix Origins.HistoryAdapters.receiveIteration w h = (.ok (result,v),k)) :
    OwnerChecks.Inv k v ∧ CurrentSlots.Inv v.wg := by
  have post := (receiveIteration w h ⟨owner,slots⟩).choose_spec.2.2
  simpa only [run] using post

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeSlotHistory
