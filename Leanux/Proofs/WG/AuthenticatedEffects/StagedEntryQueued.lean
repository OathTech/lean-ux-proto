import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueuedCarrier

/-! Whole queued-initiation suffix at its actual fixed ledger. Normal returns
expose connected native cuts for the only possible receipt. Stopped prefixes
retain the original history and an actual accounted entry or decision cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queued
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
open HandshakeSecurity.StagedDisposal

inductive NormalTrace (pid : PeerId) (w : WGWorld) (a : Ambient)
    (h : List CausalJournal.Event) : WGWorld → Ambient → List CausalJournal.Event → Prop
  | idle (native : ((decisionPrefix pid).run w).run a = .ok ((none,v),b)) :
      NormalTrace pid w a h v b h
  | repaid
      (decision : ((decisionPrefix pid).run w).run a = .ok ((some true,u),c))
      (native : ((releaseCut (some pid)).run u).run c = .ok ((none,v),b)) :
      NormalTrace pid w a h v b
        (h ++ [.stagedDisposal (.release (some pid) ⟨none,u,v,c,b⟩)])
  | queued
      (decision : ((decisionPrefix pid).run w).run a = .ok ((some false,u),c))
      (installed : ((install pid).run u).run c = .ok (((),v),b)) :
      NormalTrace pid w a h (queuedWorld pid v) b
        (h ++ [.queued ⟨CausalScope.current CausalJournal.scope? h,pid,
          ⟨(),v,queuedWorld pid v,b,b⟩⟩])

def StoppedCut (pid : PeerId) (w : WGWorld) (a : Ambient)
    (h : List CausalJournal.Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List TxLocalBatch) (stop : Stop) : Prop :=
  (((decisionPrefix pid).run w).run a = .error stop ∧ Inv h ledger debts locals w) ∨
    ∃ u c, ((decisionPrefix pid).run w).run a = .ok ((some false,u),c) ∧
      ((install pid).run u).run c = .error stop ∧ Inv h ledger debts locals u

def Result (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event)
    (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (result : Except Stop ((Unit × WGWorld) × Ambient) × List CausalJournal.Event) : Prop :=
  match result.1 with
  | .error stop => result.2 = h ∧ StoppedCut pid w a h ledger debts locals stop
  | .ok ((_,v),b) => Inv result.2 ledger debts locals v ∧ NormalTrace pid w a h v b result.2

/-- Actual queued-initiation preserves the entire indexed entry. The only
repayment is proved nonfinal from this invocation's borrow; the only other
receipt is its own work append. Stop keeps an explicit native accounted cut,
and no existing terminal result or pending ticket is discarded. -/
theorem checked (pid : PeerId) (before : Inv h ledger debts locals w) (a : Ambient) :
    Result pid w a h ledger debts locals (runWGPrefix
      (Effects.queuedWith CausalJournal.effects CausalJournal.peerRelease pid false) w a h) := by
  rw [run]
  cases first : ((decisionPrefix pid).run w).run a with
  | error stop => exact ⟨rfl,Or.inl ⟨first,before⟩⟩
  | ok out =>
    obtain ⟨⟨decision,u⟩,c⟩ := out
    have entry := decision_entry before pid a c first
    cases decision with
    | none => exact ⟨entry,.idle first⟩
    | some decision =>
      have funded := decision_funded pid a c first
      cases decision with
      | true =>
        obtain ⟨v,b,performed,native,after⟩ := repayment_total entry pid funded c
        change Result pid w a h ledger debts locals (runWGPrefix (CausalJournal.peerRelease (some pid)) u c h)
        rw [performed]
        exact ⟨after,.repaid first native⟩
      | false =>
        change Result pid w a h ledger debts locals
          (runWGPrefix (liftWGPrefix (install pid) >>= fun _ => CausalJournal.effects.append pid) u c h)
        rw [runWGPrefix,runStatePrefix_bind]
        rw [show runStatePrefix (liftWGPrefix (install pid)) u c h = (((install pid).run u).run c,h) from rfl]
        cases installed : ((install pid).run u).run c with
        | error stop => exact ⟨rfl,Or.inr ⟨u,c,first,installed,entry⟩⟩
        | ok out =>
          obtain ⟨⟨ignored,v⟩,b⟩ := out
          cases ignored
          have next := install_entry entry pid c b installed
          obtain ⟨performed,_,after⟩ := append_total next pid b
          change Result pid w a h ledger debts locals (runWGPrefix (CausalJournal.effects.append pid) v b h)
          rw [performed]
          exact ⟨after,.queued first installed⟩

/-- A completed actual callback retains the fixed ledger, native ownership,
packet bounds, and source justification, with its connected native trace. -/
theorem normal (pid : PeerId) (before : Inv h ledger debts locals w) (a b : Ambient)
    (performed : runWGPrefix
      (Effects.queuedWith CausalJournal.effects CausalJournal.peerRelease pid false) w a h =
        (.ok (((),v),b),last)) :
    Inv last ledger debts locals v ∧ NormalTrace pid w a h v b last := by
  have result := checked pid before a
  rw [performed] at result
  exact result

/-- An actual stopped callback has no unaccounted event suffix. Its native
failure is either the decision prefix or work installation after that prefix;
the latter case includes the full entry bundle at the reached decision cut. -/
theorem stopped (pid : PeerId) (before : Inv h ledger debts locals w) (a : Ambient)
    (performed : runWGPrefix
      (Effects.queuedWith CausalJournal.effects CausalJournal.peerRelease pid false) w a h =
        (.error stop,last)) :
    last = h ∧ StoppedCut pid w a h ledger debts locals stop := by
  have result := checked pid before a
  rw [performed] at result
  exact result

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queued
