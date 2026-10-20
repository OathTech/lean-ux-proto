import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSocketFront
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxPassiveFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxRepaymentWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSelectionPointFrames

/-! One source-point family for the peer transmit worker. Each constructor
is a fixed original selection, completion, cleanup or repayment interval.
This family does not claim coverage of every deeper native atom. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompleteCarrier Staged.Obligations

inductive Point (pid : PeerId) (w : World) (h : List CausalJournal.Event) : World → List CausalJournal.Event → Prop where
  | selection (point : TxSelector.Point pid w h u middle) : Point pid w h u middle
  | dead (point : TxDead.Point pid w h u middle) : Point pid w h u middle
  | cleanup (point : TxCleanup.Point pid w h u middle) : Point pid w h u middle
  | repayment (point : TxRepayment.WorkerPoint pid w h u middle) : Point pid w h u middle
  | sending (point : TxSending.Point pid w h u middle) : Point pid w h u middle
  | socket (point : TxSocket.WorkerPoint pid w h u middle) : Point pid w h u middle
  | sendFront (point : TxSendFront.WorkerPoint pid w h u middle) : Point pid w h u middle
  | accounting (point : TxPostSocket.WorkerPoint pid w h u middle) : Point pid w h u middle
  | socketFront (point : TxSocketFront.WorkerPoint pid w h u middle) : Point pid w h u middle
  | passive (point : TxPassive.Point pid w h u middle) : Point pid w h u middle

theorem Point.remaining (point : Point pid w h u middle) :
    ∃remaining,runPrefix (CausalJournal.transmit pid) w h=runPrefix remaining u middle := by
  cases point with
  | selection point=>exact point.remaining
  | dead point=>exact point.remaining
  | cleanup point=>exact point.remaining
  | repayment point=>exact point.remaining
  | sending point=>exact point.remaining
  | socket point=>exact point.remaining
  | sendFront point=>exact point.remaining
  | accounting point=>exact point.remaining
  | socketFront point=>exact point.remaining
  | passive point=>exact point.remaining

noncomputable def remainder (point : Point pid w h u middle) : PrefixM CausalJournal.Event Bool :=
  Classical.choose point.remaining

theorem remainder_run (point : Point pid w h u middle) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

inductive Evidence (initial : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (h : List CausalJournal.Event) (w : World) : Prop where
  | selection (proof : TxSelector.Evidence initial locals pid h w)
  | dead (proof : TxDead.Evidence initial locals pid h w)
  | selected (proof : TxCleanup.Evidence initial locals pid h w)
  | repayment (next : Ledger) (step : Staged.Obligations.Step initial next)
      (proof : TxRepayment.Evidence next [] locals h w)
  | socket (context : Context) (peer : context.pid=pid) (localEq : context.locals=locals)
      (origin : context.initialLedger=initial) (ledger : Ledger) (debts : List CleanupDebt)
      (step : Staged.Obligations.Step initial ledger) (proof : TxSocket.Evidence context ledger debts h w)

/-- Security: every declared peer-transmit source cut retains the original
packet lineage through selection, sending, native egress, cleanup and
reference repayment. Pending receipts remain explicit until their emission. -/
theorem Point.evidence (before : Accounted h ledger [] locals w.wg)
    (point : Point pid w h u middle) : Evidence ledger locals pid middle u := by
  cases point with
  | selection point=>exact .selection (point.evidence before)
  | dead point=>exact .dead (point.evidence before)
  | cleanup point=>exact .selected (point.evidence before)
  | repayment point=>
      obtain ⟨next,step,proof⟩:=point.evidence before
      exact .repayment next step proof
  | sending point=>exact .selected (point.evidence before)
  | socket point=>
      obtain ⟨context,peer,localEq,origin,next,debts,step,proof⟩:=point.evidence before
      exact .socket context peer localEq origin next debts step proof
  | sendFront point=>
      obtain ⟨context,peer,localEq,origin,next,debts,step,proof⟩:=point.evidence before
      exact .socket context peer localEq origin next debts step proof
  | accounting point=>
      obtain ⟨context,peer,localEq,origin,next,debts,step,proof⟩:=point.evidence before
      exact .socket context peer localEq origin next debts step proof
  | socketFront point=>
      obtain ⟨context,peer,localEq,origin,next,debts,step,proof⟩:=point.evidence before
      exact .socket context peer localEq origin next debts step proof
  | passive point=>exact .selected (point.evidence before)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxConcrete
