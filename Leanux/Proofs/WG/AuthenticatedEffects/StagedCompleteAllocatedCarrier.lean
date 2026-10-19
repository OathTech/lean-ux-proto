import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPeerCreationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePassive
import Leanux.Proofs.WG.RetirementSecurity.ReceiveEntryHolders

/-! Couple both packet-accounting directions with the native allocation invariant.
Creation derives its fresh peer-slot premise from that invariant. The native
companion is transported through the very same observed execution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteAllocated
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal StackOwnership

def Carrier (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (history : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  CompleteCarrier.Carrier debts locals history w a ∧ Allocated w

abbrev Checked (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (Safe : List Event → Prop) (action : WGPrefix Event α) : Prop :=
  StatePrefixPreserves (Carrier debts locals) Safe action

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)

theorem pair {action : WGPrefix Event α} {native : WG.M α}
    (entry : CompletePassive.Checked debts locals Safe action)
    (erases : ErasesStatePrefix action native)
    (allocated : Preserves Allocated native) : Checked debts locals Safe action := by
  intro w a h before
  obtain ⟨suffix,extended,safe,kept⟩ := entry w a h before.1
  refine ⟨suffix,extended,safe,?_⟩
  cases performed : (runPrefix (action.run w) a h).1 with
  | error reason => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    rw [performed] at kept
    exact ⟨kept,(hoare_iff_run_ambient _ _ _).mp allocated w a value v b before.2
      ((erases w a h).symm.trans performed)⟩

include accountSafe in
theorem native (action : WG.M α)
    (keeps : ∀ h ledger, Hoare action
      (fun w => CompleteCarrier.Accounted h ledger debts locals w ∧ Allocated w)
      (fun _ w => CompleteCarrier.Accounted h ledger debts locals w ∧ Allocated w)) :
    Checked debts locals Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift
  · intro h w a before
    obtain ⟨ledger,entry⟩ := before.1
    exact accountSafe ledger h w entry
  · intro h w a value v b before run
    obtain ⟨ledger,entry⟩ := before.1
    have after := (hoare_iff_run_ambient _ _ _).mp (keeps h ledger)
      w a value v b ⟨entry,before.2⟩ run
    exact ⟨⟨ledger,after.1⟩,after.2⟩

include accountSafe in
theorem create (key : Key) (psk : Option Key) :
    Checked debts locals Safe (liftWGPrefix (peerCreate key psk)) := by
  apply native Safe accountSafe
  intro h ledger
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  have fresh : PeerSlotsBounded w := before.2.choose_spec.peerSlots
  have entry := (hoare_iff_run_ambient _ _ _).mp (PeerCreationFrames.create key psk)
    w a value v b ⟨before.1.entry,fresh⟩ run
  exact ⟨⟨entry.1,before.1.complete⟩,Allocated.native (peerCreateMixed_erases key psk)
    (peerCreateMixed_preserves key psk) before.2 a b run⟩

theorem initial (net bare : Bool) : Carrier [] [] [] (Runner.initialWG net bare) a :=
  ⟨⟨[],CompleteCarrier.initial net bare⟩,⟨[],allocation_initial net bare _ rfl⟩⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteAllocated
