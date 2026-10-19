import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedOrdinaryCleanupFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedOrdinaryCleanupSource

/-! The next ordinary free comes from the same ordered cleanup path and its
fixed ledger. Both interior phases have a native account with the consumed
debt, and their total access suffix rejoins the original remaining list. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OrdinaryCleanup
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations AllocatedObligation CompletionBatch CompleteCarrier

structure Interval (context : Context) (ledger : Ledger) (debts : List CleanupDebt)
    (skb : SkbId) (rest : List SkbId) (w : World) (history : List CausalJournal.Event)
    (generation : Nat) (v : World) : Prop where
  before : Owned context (.freeing (skb :: rest)) history ledger debts w
  complete : StagedTerminalComplete.Complete history ledger
  epoch : Packets.epoch w.wg=some generation
  native : (liftWG (freeTxSkb skb)).run w=.ok ((),v)

theorem Interval.accounted
    (interval : Interval context ledger debts skb rest w history generation v)
    (phase : CleanupPrimitive.Phase) :
    Accounted (CleanupPrimitive.current phase w skb history) ledger
      (forgetFreedCell history generation skb debts)
      (⟨.selected,context.pid,rest⟩ :: context.locals) v.wg :=
  phase_accounted phase interval.before interval.complete interval.epoch interval.native

theorem Interval.literal
    (interval : Interval context ledger debts skb rest w history generation v)
    (phase : CleanupPrimitive.Phase) :
    runPrefix (CleanupPrimitive.atPhase phase w skb) w history=
      (.ok ((),v),CleanupPrimitive.current phase w skb history) :=
  CleanupPrimitive.prefix_run phase skb w v history interval.native

theorem Interval.continuation
    (interval : Interval context ledger debts skb rest w history generation v)
    (phase : CleanupPrimitive.Phase) :
    runPrefix (FirstTerminal.cleanupFree skb >>= fun _ =>
      freeLoop cleanupOps rest) w history=
      runPrefix (due phase w skb >>= fun _ =>
        freeLoop cleanupOps rest)
        v (CleanupPrimitive.current phase w skb history) := by
  rw [runPrefix_bind,runPrefix_bind,original_suffix phase w v skb history interval.native]

theorem Interval.consumed
    (interval : Interval context ledger debts skb rest w history generation v) :
    ∃ debt ∈ debts,
      (debt.ticket,Status.terminal debt.outcome)∈ledger ∧
      debt∉forgetFreedCell history generation skb debts ∧
      PacketMaterial.view v.wg skb=none :=
  native_consumes interval.before interval.epoch interval.native

/-- The actual next cleanup's successor carries exactly the canonical
filtered debts. No new ledger is chosen for an interior point. -/
theorem head_interval
    (path : CleanupPath context ledger (skb :: rest) debts w history v last) :
    ∃ generation nextWorld,
      Interval context ledger debts skb rest w history generation nextWorld ∧
      CleanupPath context ledger rest (forgetFreedCell history generation skb debts)
        nextWorld (finished w skb history) v last := by
  cases path with
  | next before complete generation epoch performed tail =>
      have native := (FirstTerminal.cleanupFree_erases skb w history).symm.trans (congrArg Prod.fst performed)
      have equal := congrArg Prod.snd
        (performed.symm.trans (CleanupPrimitive.cleanup_run skb w _ history native))
      change history ++ _ = finished w skb history at equal
      rw [equal] at tail
      exact ⟨generation,_,⟨before,complete,epoch,native⟩,tail⟩

/-- Every source-selected list position has its own actual erase and
consumed debt, whether the enclosing worker later returns or stops. -/
theorem prefix_interval (done : List SkbId)
    (path : CleanupPath context ledger (done ++ skb :: rest) debts w history v last) :
    ∃ cutWorld cutHistory cutDebts generation nextWorld,
      runPrefix (freeLoop cleanupOps done) w history=
        (.ok ((),cutWorld),cutHistory) ∧
      Interval context ledger cutDebts skb rest cutWorld cutHistory generation nextWorld ∧
      CleanupPath context ledger rest (forgetFreedCell cutHistory generation skb cutDebts)
        nextWorld (finished cutWorld skb cutHistory) v last := by
  obtain ⟨cutWorld,cutHistory,cutDebts,performed,_,_,tail⟩ := path.split done
  obtain ⟨generation,nextWorld,interval,remaining⟩ := head_interval tail
  exact ⟨cutWorld,cutHistory,cutDebts,generation,nextWorld,performed,interval,remaining⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OrdinaryCleanup
