import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionHistoryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPhysicalFrames

/-! Fixed-ticket transport through the actual admission/publication source.
Normal returned cuts retain physical backing and exact queued-or-held ownership.
Every Stop retains the original allocation records and mixed ticket uniqueness;
that history certificate is not a stopped physical ownership theorem. Refusal
terminal settlement and free-loop transport remain separate source contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Admission
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity
set_option maxHeartbeats 600000

def Entry (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (history : List CausalJournal.Event) (w : World) : Prop :=
  Physical history ledger debts w.wg ∧
    TxCoverage (⟨.unpublished,pid,items⟩ :: locals) w.wg ∧
    TxInventory (⟨.unpublished,pid,items⟩ :: locals) w.wg

def Returned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (ret : Int) (history : List CausalJournal.Event) (w : World) : Prop :=
  Physical history ledger debts w.wg ∧ CreateCoverage locals pid items ret w.wg ∧
    CreateOccurrences locals pid items ret w.wg

/-- The full original admission prefix uses the same selected fixed ledger.
On any Stop, all its assigned allocation occurrences and ticket uniqueness
remain in the retained actual history. Physical claims are made only at the
returned native cut, with the original return code deciding queued or held. -/
theorem actual_contract (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) :
    PrefixEnsures (Entry ledger debts locals pid items)
      (fun h => Recorded h ledger debts ∧ MixedInjective h ledger debts)
      (actual pid items) (Returned ledger debts locals pid items) := by
  intro w h before
  obtain ⟨suffix,grown⟩ := actual_appends pid items w h
  have historySafe : Recorded (runPrefix (actual pid items) w h).2 ledger debts ∧
      MixedInjective (runPrefix (actual pid items) w h).2 ledger debts := by
    rw [grown]
    exact ⟨before.1.recorded.append suffix,before.1.recorded.mixed_append before.1.mixed suffix⟩
  refine ⟨suffix,grown,historySafe,?_⟩
  cases result : (runPrefix (actual pid items) w h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨ret,v⟩ := out
    have full := (actual_erases pid items w h).symm.trans result
    rw [liftWG_run] at full
    cases native : ((RxCredits.createReturnSource pid items).run w.wg).run w.ambient with
    | error stop => simp [native,Except.map] at full
    | ok out =>
      obtain ⟨⟨returned,g⟩,ambient⟩ := out
      simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
      obtain ⟨rfl,rfl⟩ := full
      have same := (ProjectedAction.iff_run_ambient _ _ _).mp
        (native_front pid items) w.wg w.ambient returned g ambient native
      have physical := before.1.views (congrArg Prod.fst same) (congrArg Prod.snd same)
      change Physical _ _ _ g ∧ CreateCoverage _ _ _ returned g ∧ CreateOccurrences _ _ _ returned g
      rw [grown]
      exact ⟨physical.append suffix,before.2.1.create_return _ _ native,
        before.2.2.create_return _ _ native⟩

/-- A completed native allocation assigns the actual selected ticket list
by ordinal, then enters the exact admission source with its unpublished batch.
The returned contract also covers a later admission Stop without assuming the
enclosing createData call completed. Refusal cleanup is still the next cut. -/
theorem allocated_admission_entry
    (validLedger : Valid births ledger) (physical : Physical history ledger debts run.before)
    (bounded : Packets.Inv run.before) (ownership : TxCoverage locals run.before)
    (inventory : TxInventory locals run.before) (pid : PeerId) (packets : List DataPacket)
    (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d)
    (aligned : Aligned related (pendingAt (.selected takePosition) ledger) packets) :
    let assigned := assignBatch takePosition history.length ledger
    let events := history ++ [.old (.allocated packets run)]
    let start := NativeAdapter.world run.after run.ambientAfter
    TransmitSecurity.Staged.Obligations.Step ledger assigned ∧ Valid births assigned ∧
      Entry assigned debts locals pid run.value events start ∧
      PrefixEnsures (Entry assigned debts locals pid run.value)
        (fun h => Recorded h assigned debts ∧ MixedInjective h assigned debts)
        (actual pid run.value) (Returned assigned debts locals pid run.value) := by
  have assigned := allocate_mixed_covered validLedger physical.resident physical.mixed physical.covered
    physical.cleanup bounded ownership inventory pid packets valid device aligned
  refine ⟨assigned.1,assigned.2.1,?_,actual_contract _ debts locals pid run.value⟩
  exact ⟨⟨assigned.2.2.1,assigned.2.2.2.2.1,assigned.2.2.2.2.2.1,assigned.2.2.2.1⟩,
    assigned.2.2.2.2.2.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Admission
