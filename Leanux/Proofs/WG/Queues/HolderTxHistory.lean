import Leanux.Proofs.WG.Queues.TxHolderStep
import Leanux.Proofs.WG.Queues.HolderEncryptHistory
import Leanux.Proofs.WG.Queues.SchedulerPreservation

/-! Complete holder accounting through the actual TX iteration and its
activation pre-step. The pre-step may run encryption and NAPI, so its actual
RX removal suffix is retained at the original fixed journal boundary. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderTxHistory
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders HolderEncrypt

/-- The real TX step and rescheduling decision retain the complete account. -/
theorem txIter_boundary (pid : PeerId) :
    Preserves (fun w : World => Boundary cs loans w.wg)
      (WG.txIter pid (Env.condResched .txWorker)) := by
  unfold WG.txIter workerIter
  apply preserves_bind (lift_boundary (txStep_boundary pid))
  intro more
  split
  · exact preserves_pure _
  · apply preserves_bind
    · apply preserves_bind (product_store_boundary (condResched_sameKernel .txWorker))
      intro need
      exact productAmbient_spec (AmbientM.branch .txNeedResched need) _ (fun _ _ hi => hi)
    · intro yielded
      split <;> exact preserves_pure _

/-- The original mixed lifetime observer introduces no RX removal record. -/
theorem txIter_at (pid : PeerId) (hi : HolderNapi.At initial loans before h w)
    (run : runPrefix (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker))))
      w h = (.ok (result,v),k)) : HolderNapi.At initial loans before k v :=
  mixed_at _ _ (txIterPrefix_erases pid (erasesPrefix_lift _))
    (fun _ => txIter_boundary pid) hi run

theorem txIter_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) := by
  apply NapiCarrier.normal_spec (Appends.focus _ _ _)
  intro w h result v hi run
  exact txIter_at pid hi (Prod.ext run rfl)

private theorem mixed_preserves (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (keeps : ∀ cs, Preserves (fun w : World => Boundary cs loans w.wg) a) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) (RxHistory.mixed g) := by
  apply NapiCarrier.normal_spec (Appends.focus _ _ _)
  intro w h x v hi run
  exact mixed_at g a erases keeps hi (Prod.ext run rfl)

/-- Only the TX scheduling alias changes; every funded holder field remains. -/
theorem work_fields (f : List PeerId → List PeerId) :
    SameView HolderEncrypt.fields (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  cases hd : w.dev <;> simp [hd,rxView]

private theorem peer_fields (pid : PeerId) : SameView HolderEncrypt.fields (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg HolderEncrypt.fields (getPeer_normal pid w v p a b run).1

private theorem encrypt_preserves :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) RxHistory.encryptIteration := by
  apply NapiCarrier.normal_spec
    (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.encryptIteration_appends)
  intro w h x v hi run
  exact HolderEncrypt.iteration_normal hi (Prod.ext run rfl)

/-- Actual crypt-ahead carries the same accounting cut through its optional
committed encryption and NAPI, including the two TX work-queue updates. -/
theorem cryptAhead_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) (RxHistory.cryptAhead pid) := by
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
        (RxHistory.mixed (liftPrefix (monadLift a : Leanux.M α))) :=
    mixed_preserves _ _ (erasesPrefix_lift _) (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))
  have stopped {α : Type} (e : Stop) :
      PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
        (RxHistory.mixed (throw e : PrefixM LifetimeEvent α)) :=
    mixed_preserves _ _ (erasesPrefix_throw e) (fun _ => hoare_throw e)
  have peer (id : PeerId) := mixed_preserves (loans := loans) (initial := initial) (before := before)
    _ _ (liftWGObserver_erases (getPeerMixed_erases id))
    (fun _ => lift_boundary (native_boundary (peer_fields id)))
  have packet (id : SkbId) := mixed_preserves (loans := loans) (initial := initial) (before := before)
    _ _ (liftWGObserver_erases (getTxSkbPrefix_erases id))
    (fun _ => lift_boundary (native_boundary (getTx_fields id)))
  have work (f : List PeerId → List PeerId) := mixed_preserves (loans := loans) (initial := initial) (before := before)
    _ _ (liftWGObserver_erases (erasesStatePrefix_lift (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})))
    (fun _ => lift_boundary (native_boundary (work_fields f)))
  unfold RxHistory.cryptAhead
  repeat' first
    | (scheduler_preserve_at RxHistory.encryptIteration; exact encrypt_preserves)
    | (scheduler_preserve_at getPeerMixed; exact peer _)
    | (scheduler_preserve_at getTxSkbPrefix; exact packet _)
    | (scheduler_preserve_at modifyDev; first
        | exact work (fun q => q ++ [pid])
        | exact work (fun q => q.erase pid))
    | (scheduler_preserve_at throw; exact stopped _)
    | (scheduler_preserve_at getAmbient; exact ambient (get : AmbientM Ambient))
    | (scheduler_preserve_at peekHiddenSite; exact ambient AmbientM.peekHiddenSite)
    | (scheduler_preserve_at modifyAmbient; exact ambient (modify _ : AmbientM Unit))
    | (scheduler_preserve_at invariant; exact ambient (AmbientM.invariant _))
    | (scheduler_preserve_at Pure.pure; exact PrefixPreserves.pure (fun _ _ _ => True.intro) _)
    | (scheduler_preserve_at Bind.bind; apply PrefixPreserves.bind)
    | maintenance_intro
    | (scheduler_preserve_at ite; split)
    | (scheduler_preserve_at dite; split)
    | (with_reducible split)
    | dsimp (config := {failIfUnchanged := true}) only

/-- TX activation iteration includes the actual crypt-ahead callback. -/
theorem activationIteration_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (a : Activation) (worker : a.worker = .txWorker) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) (RxHistory.activationIteration a) := by
  unfold RxHistory.activationIteration
  rw [worker]
  cases pid : a.pid with
  | none =>
    exact mixed_preserves _ _ (erasesPrefix_lift _)
      (fun _ => productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi))
  | some p =>
    exact PrefixPreserves.bind (cryptAhead_preserves initial loans before p)
      (fun _ => txIter_preserves initial loans before p)

end Leanux.Proofs.WG.Queues.RxCredits.HolderTxHistory
