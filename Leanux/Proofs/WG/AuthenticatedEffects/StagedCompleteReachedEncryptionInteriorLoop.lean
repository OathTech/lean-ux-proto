import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionInteriorCoverage

/-! Ordered coverage for the whole actual packet loop, on every outcome.
Each executed child carries its actual input world and the same ledger.
DEAD ends the original loop; it does not execute the remaining batch members. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open CompleteCarrier EncryptionPacket

inductive Execution (headId : SkbId) (head : RunWitness DataPacket)
    (ledger : Staged.Obligations.Ledger) (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch) :
    List SkbId → PacketState → World → List CausalJournal.Event →
      Except Stop (PacketState × World) → List CausalJournal.Event → Prop where
  | nil (accounted : Accounted history ledger debts locals w.wg) :
      Execution headId head ledger debts locals [] state w history (.ok (state,w)) history
  | stopped {skb : SkbId} (accounted : Accounted history ledger debts locals w.wg)
      (performed : runPrefix (iteration headId head skb state) w history = (.error reason,last)) :
      Execution headId head ledger debts locals (skb :: rest) state w history (.error reason) last
  | done {skb : SkbId} (accounted : Accounted history ledger debts locals w.wg)
      (performed : runPrefix (iteration headId head skb state) w history = (.ok (.done next,v),last))
      (returned : Accounted last ledger debts locals v.wg) :
      Execution headId head ledger debts locals (skb :: rest) state w history (.ok (next,v)) last
  | yielded {skb : SkbId} (accounted : Accounted history ledger debts locals w.wg)
      (performed : runPrefix (iteration headId head skb state) w history = (.ok (.yield next,u),middle))
      (tail : Execution headId head ledger debts locals rest next u middle outcome last) :
      Execution headId head ledger debts locals (skb :: rest) state w history outcome last

theorem Execution.source (path : Execution headId head ledger debts locals items state w history outcome last) :
    runPrefix (loop headId head items state) w history = (outcome,last) := by
  induction path with
  | nil => rfl
  | stopped _ performed => rw [loop_cons,runPrefix_bind,performed]
  | done _ performed _ => rw [loop_cons,runPrefix_bind,performed]; rfl
  | yielded _ performed _ ih => rw [loop_cons,runPrefix_bind,performed]; exact ih

/-- Original successful and stopped runs both generate the ordered source
path. Packet-point classification is available at every constructor's actual
accounted input, rather than only at a selected failed iteration. -/
theorem execution (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (loop headId head items state) w history = (outcome,last)) :
    Execution headId head ledger debts locals items state w history outcome last := by
  induction items generalizing state w history with
  | nil => cases performed; exact .nil before
  | cons skb rest ih =>
    rw [loop_cons,runPrefix_bind] at performed
    cases current : runPrefix (iteration headId head skb state) w history with
    | mk result middle =>
      rw [current] at performed
      cases result with
      | error reason => cases performed; exact .stopped before current
      | ok out =>
        obtain ⟨choice,u⟩ := out
        have account := iteration_accounted before current
        cases choice with
        | done next => cases performed; exact .done before current account
        | yield next => exact .yielded before current (ih account performed)

theorem Execution.normal_accounted
    (path : Execution headId head ledger debts locals items state w history (.ok (next,v)) last)
    (before : Accounted history ledger debts locals w.wg) : Accounted last ledger debts locals v.wg :=
  loop_accounted before path.source

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
