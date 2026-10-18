import Leanux.Proofs.WG.RetirementSecurity.OccurrenceEncryptFrames

/-! Complete native encryption iterations transfer the live ring alias to
an explicit local before softirq, then consume that local exactly once. The
allocation witness and physical packet ownership survive the real callback. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceEncrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open Queues.RxCredits OccurrenceStack

theorem step (item : Option (List SkbId)) :
    Hoare (RxWorkers.encryptStepTailSource item)
      (fun w : World => TxOccurrences locals (item.toList ++ active) w.wg)
      (fun _ w => TxOccurrences locals active w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases item with
  | none => cases run; exact before
  | some items => exact ⟨(hoare_iff_run _ _ _).mp (tail_inventory (some items)) w result v before.1 run,
      before.2.complete run⟩

theorem tail_occurrences (item : Option (List SkbId)) :
    Hoare (RxWorkers.encryptTailSource item)
      (fun w : World => TxOccurrences locals (item.toList ++ active) w.wg)
      (fun _ w => TxOccurrences locals active w.wg) := by
  let P := fun w : World => TxOccurrences locals active w.wg
  have need : Preserves P (Env.condResched .encryptWorker) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    have device := congrArg (fun s : ProductStore43 => s.2.2.2.dev)
      ((ProjectedAction.iff_run _ _ _).mp (condResched_sameKernel _) w result v run)
    change v.wg.dev = w.wg.dev at device
    exact ⟨before.1.wire_queues (by simp only [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,device])
        (by funext pid; simp only [handoffTxView,device]),
      before.2.frame_packets (by simp only [TxRing.nativeCell,device])
        (fun _ owned => owned.queues (by funext pid; simp only [handoffTxView,device]))
        (by funext id; simp only [TxDisposition.txPackets,device])⟩
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  unfold RxWorkers.encryptTailSource workerIter
  apply hoare_bind _ _ (step item)
  intro processed
  change Preserves P _
  routing_tx_source [] using [need,ambient]

theorem tail (before : Ready locals (item.toList ++ active) w.wg)
    (run : (RxWorkers.encryptTailSource item).run w = .ok (result,v)) : Ready locals active v.wg := by
  refine ⟨?_,(hoare_iff_run _ _ _).mp (tail_occurrences item) w result v before.2 run⟩
  obtain ⟨history,account⟩ := before.1
  obtain ⟨_,_,_,post⟩ := RxWorkers.encryptTail_preserves item w history account
  have observed := RxWorkers.encryptTail_erases item w history
  rw [run] at observed
  rw [observed] at post
  exact ⟨_,post⟩

theorem iteration : Preserves (fun w : World => Ready locals active w.wg)
    (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  rw [RxWorkers.encrypt_source,MaterialOrigin.bind_ok] at run
  obtain ⟨item,u,pollRun,run⟩ := run
  have polled : Ready locals (item.toList ++ active) u.wg := by
    rw [liftWG_run] at pollRun
    cases native : (TxRing.pollSource.run w.wg).run w.ambient with
    | error e => simp [native,Except.map] at pollRun
    | ok output =>
      obtain ⟨⟨out,g⟩,a⟩ := output
      simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at pollRun
      obtain ⟨rfl,rfl⟩ := pollRun
      exact poll before w.ambient a native
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨_,t,callback,tailRun⟩ := run
  exact tail ((hoare_iff_run _ _ _).mp (OccurrenceNapi.softirq locals (item.toList ++ active))
    u () t polled callback) tailRun

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceEncrypt
