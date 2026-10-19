import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeDecrypt

/-! Native encryption consumes its unique active batch. Successful byte
installation covers all members before CRYPTED publication; the actual worker
wrapper and NAPI callbacks retain this guarantee. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Encrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open RetirementSecurity Queues.RxCredits Native Stack

theorem step_inv (item : Option (List SkbId)) :
    Hoare (RxWorkers.encryptStepTailSource item)
      (fun w : World=>Coherent locals (item.toList++active) w.wg)
      (fun _ w=>Inv w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases item with
  | none=>cases run; exact before.2
  | some items=>exact native_tail_preserves items before.1 before.2 run

theorem tail_inv_full (item : Option (List SkbId)) :
    Hoare (RxWorkers.encryptTailSource item)
      (fun w : World=>Coherent locals (item.toList++active) w.wg)
      (fun _ w=>Inv w.wg) := by
  let P:=fun w : World=>Inv w.wg
  have need : Preserves P (Env.condResched .encryptWorker) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    have same:=congrArg (fun s : ProductStore43=>s.2.2.2.dev)
      ((ProjectedAction.iff_run _ _ _).mp (condResched_sameKernel _) w result v run)
    change v.wg.dev=w.wg.dev at same
    apply before.frame
    dsimp only [view]
    apply Prod.ext
    · funext pid; simp only [handoffTxView,same]
    · funext id; simp only [TxDisposition.txPackets,same]
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before=>before)
  unfold RxWorkers.encryptTailSource workerIter
  apply hoare_bind _ _ (step_inv item)
  intro processed
  change Preserves P _
  routing_tx_source [] using [need,ambient]

theorem tail (before : Coherent locals (item.toList++active) w.wg)
    (run : (RxWorkers.encryptTailSource item).run w=.ok (result,v)) : Coherent locals active v.wg :=
  ⟨OccurrenceEncrypt.tail before.1 run,
    (hoare_iff_run _ _ _).mp (tail_inv_full item) w result v before run⟩

theorem poll_inv : Preserves Inv TxRing.pollSource := by
  have read := Native.store getDev_sameWGStore
  have edit (queue : PtrRing (List SkbId)) : Preserves Inv (modifyDev fun d => {d with encryptQueue := queue}) :=
    ReadyCiphertext.modify_device _ (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) := hoare_liftAmbient a Inv
  rxstack_preserves_source [TxRing.pollSource] using [read,edit,ambient]

theorem poll (before : Coherent locals active w) (a b : Ambient)
    (run : (TxRing.pollSource.run w).run a = .ok ((item,v),b)) :
    Coherent locals (item.toList ++ active) v :=
  ⟨OccurrenceEncrypt.poll before.1 a b run,
    (hoare_iff_run_ambient _ _ _).mp poll_inv w a item v b before.2 run⟩

theorem iteration : Preserves (fun w : World => Coherent locals active w.wg)
    (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  rw [RxWorkers.encrypt_source,MaterialOrigin.bind_ok] at run
  obtain ⟨item,u,pollRun,run⟩ := run
  have polled : Coherent locals (item.toList ++ active) u.wg := by
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
  exact tail ((hoare_iff_run _ _ _).mp (Napi.softirq locals (item.toList ++ active))
    u () t polled callback) tailRun

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Encrypt
