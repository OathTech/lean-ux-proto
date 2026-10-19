import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteAccounted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSource

/-! A stopped completion account has a named failed callback, native saved
entry and phase-derived active local. The callback evidence and account use
the same record. Reach from an enclosing caller is a separate, stronger field. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch
open AllocatedObligation.CompletionBatch.Converse

variable {context : Context} {ledger : Ledger} {debts : List CleanupDebt}

inductive Action where
  | callback (site : Site)
  | releaseCut (peer : Option PeerId)
  | releaseFinish (value : Option (PeerId × Peer))

def Action.source : Action → PrefixM CausalJournal.Event Unit
  | .callback site => site.action
  | .releaseCut peer => do
      _ ← liftWGObserver (PeerRelease.cut peer)
      pure ()
  | .releaseFinish value => PeerRelease.finish value

structure Cut (context : Context) where
  ledger : Ledger
  debts : List CleanupDebt
  phase : Phase
  world : World
  before : List CausalJournal.Event
  action : Action

def Cut.locals (cut : Cut context) : List TxLocalBatch :=
  ⟨.selected,context.pid,cut.phase.active context⟩ :: context.locals

/-- The saved native entry is not a returned world of a failed action. -/
structure Cut.Valid (cut : Cut context) (reason : Stop)
    (last : List CausalJournal.Event) : Prop where
  failed : runPrefix cut.action.source cut.world cut.before = (.error reason,last)
  accounted : Accounted last cut.ledger cut.debts cut.locals cut.world.wg

def Cut.indexed (frontier : IndexedFrontier context ledger debts reason last) : Cut context :=
  ⟨ledger,debts,frontier.phase,frontier.world,frontier.before,.callback frontier.site⟩

theorem Cut.indexed_valid (frontier : IndexedFrontier context ledger debts reason last)
    (complete : Complete last ledger) : (Cut.indexed frontier).Valid reason last :=
  ⟨frontier.nativeFailure,indexed_frontier_accounted frontier complete⟩

/-- This certificate connects the saved entry to a supplied enclosing bind
decomposition. A native source-site or snapshot anchor remains necessary before
using it as an initialized reachability claim; extensional factorization alone
does not provide that anchor. -/
structure Failure (context : Context) (body : PrefixM CausalJournal.Event α)
    (w : World) (history : List CausalJournal.Event) (reason : Stop)
    (last : List CausalJournal.Event) where
  cut : Cut context
  valid : cut.Valid reason last
  reached : At cut.action.source cut.world cut.before body w history

theorem Failure.run (witness : Failure context body w history reason last) :
    runPrefix body w history = (.error reason,last) :=
  witness.reached.failure witness.valid.failed

theorem Failure.accounted (witness : Failure context body w history reason last) :
    Accounted last witness.cut.ledger witness.cut.debts witness.cut.locals witness.cut.world.wg :=
  witness.valid.accounted

theorem indexed_failure (frontier : IndexedFrontier context ledger debts reason last)
    (complete : Complete last ledger)
    (reached : At frontier.site.action frontier.world frontier.before body w history) :
    Nonempty (Failure context body w history reason last) :=
  ⟨⟨Cut.indexed frontier,Cut.indexed_valid frontier complete,reached⟩⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
