import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixPassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSavedSource

/-! Saved peer metadata retains the full carrier and all journal prefixes.
The actions here are literal native lifts with unchanged histories. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationSaved
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem read (pid : PeerId) : StateEnsures (CompleteCarrier.Carrier debts locals) Safe
    (liftWGPrefix (getPeer pid)) (fun p=>CompleteSaved.Saved debts locals pid p) :=
  StateEnsures.quiet (CompleteSaved.read Safe accountSafe pid) (fun _ _ _=>rfl)

theorem store (pid : PeerId) (p : Peer) (action : WG.M α) (same : SameWGStore action) :
    StateEnsures (CompleteSaved.Saved debts locals pid p) Safe (liftWGPrefix action)
      (fun _=>CompleteSaved.Saved debts locals pid p) :=
  StateEnsures.quiet (CompleteSaved.store Safe accountSafe pid p action same) (fun _ _ _=>rfl)

theorem write (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue) :
    StateEnsures (CompleteSaved.Saved debts locals pid p) Safe (liftWGPrefix (setPeer pid (f p)))
      (fun _=>CompleteCarrier.Carrier debts locals) :=
  StateEnsures.quiet (CompleteSaved.write Safe accountSafe pid p f same) (fun _ _ _=>rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationSaved
