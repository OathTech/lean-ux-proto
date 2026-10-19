import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadySource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCompleteCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteLedgerFrames

/-! The active selected frontier carries complete accounting on the same
fixed ledger as its native take anchor and material/ownership prerequisites.
It is distinct from idle Entry, including on failed borrowing or nonce checks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal StagedTerminalComplete CompleteCarrier
open HandshakeSecurity.StagedConservation

structure Ready (ledger : Ledger) (debts : List CleanupDebt) (locals : List RetirementSecurity.TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (history : List Event) (w : WGWorld) (a : Ambient) : Prop
    extends toReady : ReadyCarrier.Ready ledger debts locals generation pid peer position history w a where
  complete : Complete history ledger

def Active (ledger : Ledger) (debts : List CleanupDebt) (generation : Nat) (pid : PeerId)
    (peer : Peer) (position : Nat) (history : List Event) : Prop :=
  SoundHeld.Active ledger debts generation pid peer position history ∧ Complete history ledger

theorem Ready.active (before : Ready ledger debts locals generation pid peer position history w a) :
    Active ledger debts generation pid peer position history := ⟨before.toSound.active,before.complete⟩

/-- The selected ledger is the exact native take transfer. No separate
successor is chosen for its terminal-receipt completeness. -/
theorem taken (r : Take.Receipt) (native : r.Valid) (chosen : r.run.value = some peer)
    (before : Accounted history ledger debts locals r.run.before) :
    ∃ after generation, Staged.Obligations.Step ledger after ∧
      after = transferLocation (.staged generation r.pid peer.internalId) (.selected history.length) ledger ∧
      Ready after debts locals generation r.pid peer history.length
        (history ++ [.stagingTaken r]) r.run.after r.run.ambientAfter := by
  obtain ⟨after,accounted,core⟩ := core_take r native before.entry.core
  have transfer := accounted.exactTransfer
  rw [chosen] at transfer
  obtain ⟨generation,epoch,sameLedger,_,aligned⟩ := transfer
  obtain ⟨_,_,same,_,empty,_⟩ := take_receipt_views r native peer chosen
  have vacant : RestoreEntry.Vacant generation r.pid peer.internalId r.run.after := ⟨same.trans epoch,empty⟩
  have base : HeldFrontier.Held after debts generation r.pid peer history.length
      (history ++ [.stagingTaken r]) r.run.after r.run.ambientAfter :=
    ⟨core,vacant,aligned,⟨history,[],r,by simp,rfl,rfl,native,chosen,core,vacant,aligned,by simp⟩⟩
  refine ⟨after,generation,accounted.step,sameLedger,⟨⟨⟨base,?_,?_,?_⟩,?_⟩,?_⟩⟩
  · rw [sameLedger]
    exact (before.entry.justified.transfer _ _).append _
  · rw [sameLedger]
    exact (before.entry.allocationLinks.transferred _ _ (by intros; simp) (by intros; simp)).append _
  · exact take_selected_only r chosen accounted before.entry.noSelected
  · exact TakeFrames.physical before.entry native
  · rw [sameLedger]
    exact (before.complete.transferred _ _).append_quiet
      (fun _ member => by cases List.mem_singleton.mp member; intro position; rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
