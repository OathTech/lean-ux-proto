import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeIntervals

/-! Every initialized evidence family is interpreted as the semantic current
account or one of the fixed mutation intervals. Family wrappers do not remain
as an arbitrary acceptance premise at the resulting claim. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations RetirementSecurity AllocatedObligation CompleteCarrier

theorem Classified.of_peer (proof : PeerRetirement.Points.Evidence ledger debts locals h w) : Classified h w := by
  cases proof with
  | accounted account=>
      obtain ⟨_,_,_,before⟩:=account
      exact .of_accounted before
  | pending peer value origin target clock next before native after=>exact Or.inr (.release before native)

theorem Classified.of_nested (proof : NestedPeer.Evidence ledger debts locals h w) : Classified h w.wg := by
  cases proof with
  | accounted account=>
      obtain ⟨_,_,_,before⟩:=account
      exact .of_accounted before
  | pending peer value origin before native after=>exact Or.inr (.nestedRelease before native)
  | nativeErased peer pid p origin before checked after=>exact Or.inr (.nestedErase before checked)

theorem Classified.of_create_live (proof : CreatePhase.Live ledger debts locals pid items h w) : Classified h w := by
  obtain ⟨_,_,_,before⟩:=proof.accounted
  exact .of_accounted before

theorem Classified.of_create_phase (proof : CreatePhase.Evidence ledger debts locals pid items h w) : Classified h w.wg := by
  cases proof with
  | live account=>exact .of_create_live account
  | awaiting current steps reason done ordered settled cut phase=>exact Or.inr (.createFree cut phase)

theorem Classified.of_creation (proof : CreateExpanded.Evidence ledger debts locals pid items h w) : Classified h w.wg := by
  cases proof with
  | phase evidence=>exact .of_create_phase evidence
  | release current active steps evidence=>exact .of_nested evidence

theorem Classified.of_staging_phase (proof : StagingPhase.Evidence ledger debts locals h w a) : Classified h w := by
  cases proof with
  | accounted current steps account=>exact .of_accounted account
  | selected current steps ready=>exact .of_selected ready
  | taking current steps cut=>exact Or.inr (.taking cut)
  | restoring current steps cut=>exact Or.inr (.restoring cut)
  | created assigned steps live=>exact .of_create_live live

theorem Classified.of_staging (proof : StagingExpanded.Evidence ledger debts locals h w a) : Classified h w := by
  cases proof with
  | phase evidence=>exact .of_staging_phase evidence
  | allocation current steps cut=>exact Or.inr (.allocating cut)
  | creation evidence=>exact .of_creation evidence

theorem Classified.of_preparation
    (proof : StagingPhase.PreparationPhase h ledger debts locals pid w a middle v b) : Classified middle v := by
  cases proof with
  | idle before=>exact .of_accounted before
  | pending before device resident empty allocated=>exact Or.inr (.keepalive before device resident empty allocated)
  | recorded ready after native account change=>exact .of_accounted account

theorem Classified.of_keepalive_phase
    (proof : StagingPhase.KeepaliveEvidence h ledger debts locals pid w a middle v b) : Classified middle v := by
  cases proof with
  | preparation phase=>exact .of_preparation phase
  | staging after prepared account change phase=>exact .of_staging_phase phase

theorem Classified.of_keepalive
    (proof : KeepaliveExpanded.Evidence ledger debts locals pid w a h middle v b) : Classified middle v := by
  cases proof with
  | canonical phase=>exact .of_keepalive_phase phase
  | staging entered prepared account change phase=>exact .of_staging phase

theorem Classified.of_selector (proof : TxSelector.Evidence ledger locals pid h w) : Classified h w.wg := by
  cases proof with
  | idle after steps account=>exact .of_accounted account
  | selected items account pending=>exact .of_accounted account

theorem Classified.of_dead (proof : TxDead.Evidence ledger locals pid h w) : Classified h w.wg := by
  cases proof with
  | boundary next items step account pending=>exact .of_accounted account
  | primitive step waiting=>exact Or.inr (.deadFree waiting)

theorem Classified.of_cleanup (proof : TxCleanup.Evidence ledger locals pid h w) : Classified h w.wg := by
  obtain ⟨_,_,_,_,account⟩:=proof
  exact .of_accounted account

theorem Classified.of_repayment (proof : TxRepayment.Evidence ledger debts locals h w) : Classified h w.wg := by
  cases proof with
  | accounted next step account=>exact .of_accounted account
  | peer evidence=>exact .of_nested evidence

theorem Classified.of_socket (proof : TxSocket.Evidence context ledger debts h w) : Classified h w.wg := by
  cases proof with
  | accounted next nextDebts step account=>exact .of_accounted account
  | pending point=>exact Or.inr (.socket point)

theorem Classified.of_tx (proof : TxConcrete.Evidence ledger locals pid h w) : Classified h w.wg := by
  cases proof with
  | selection evidence=>exact .of_selector evidence
  | dead evidence=>exact .of_dead evidence
  | selected evidence=>exact .of_cleanup evidence
  | repayment next step evidence=>exact .of_repayment evidence
  | socket context peer localEq origin next debts step evidence=>exact .of_socket evidence

theorem Classified.of_trim (proof : Transmit.Front.TrimPoints.Evidence h ledger debts locals pid w a) : Classified h w := by
  cases proof with
  | accounted before=>exact .of_accounted before
  | iteration cut=>exact Or.inr (.trimLoop cut)
  | guarded cut device resident=>exact Or.inr (.trimLoop cut)
  | dropped cut device resident excess=>exact Or.inr (.trimDrop cut device resident excess)
  | returned before performed=>exact Or.inr (.trimReturned before performed)

theorem Classified.of_front (proof : FrontCuts.Evidence ledger debts locals h w a) : Classified h w := by
  cases proof with
  | accounted current step account=>exact .of_accounted account
  | trim point=>exact .of_trim point
  | pendingRouted before path=>exact Or.inr (.routed before path)

theorem Evidence.classified (proof : Evidence h w) : Classified h w := by
  cases proof with
  | accounted ledger account=>exact .of_accounted account
  | purge pending=>
      cases pending with
      | cleared before device resident=>exact Or.inr (.purge before device resident)
  | peer ledger evidence=>exact .of_peer evidence
  | staging ledger evidence=>exact .of_staging evidence
  | front ledger evidence=>exact .of_front evidence
  | keepalive ledger evidence=>exact .of_keepalive evidence
  | transmit ledger pid evidence=>exact .of_tx evidence

/-- Security: each declared initialized point has the same-ledger native
ticket partition or one fixed mutation interval carrying its original cohort,
aliases or pending receipt. No phase-interpretation premise is assumed. -/
theorem initialized_classification (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    Runner.Points.Covered (children nativeConsume nativeNapi nativeWorker nativeWork nativeDispatch)
      (fun h w=>Classified h w.wg) (Runner.Points.executeShape trace placeholders) [] := by
  intro site u middle point
  exact (initialized trace placeholders site u middle point).classified

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
