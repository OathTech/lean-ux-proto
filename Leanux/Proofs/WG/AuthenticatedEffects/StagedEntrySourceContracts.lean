import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryFront
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeepaliveSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryOriginalRelease

/-! Bind-compatible entry contracts for the actual front, keepalive and
original release. The source-specific theorems retain the stronger cut and
settlement records; these adapters forget them only for sequential transport. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Source
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation Staged.Obligations CausalJournal
open HandshakeSecurity.StagedConservation

def Carrier (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (history : List Event) (w : WGWorld) (_ : Ambient) : Prop :=
  ∃ ledger, Inv history ledger debts locals w

theorem front_appends (input : StagedAdmission.Front.Input) : StateAppends
    (CausalJournal.front input.family input.address input.packets input.mtu) := by
  unfold CausalJournal.front Front.observed
  apply StateAppends.bind
  · intro w a h; exact ⟨[_],rfl⟩
  · intro _
    exact (Front.front_appends (Front.observedOps_appends _ _) _ _ _ _).receiptWGObserved _

theorem front (input : StagedAdmission.Front.Input) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h) :
    StatePrefixPreserves (Carrier debts locals) Safe
      (CausalJournal.front input.family input.address input.packets input.mtu) := by
  intro w a h before
  obtain ⟨ledger,entry⟩ := before
  obtain ⟨suffix,extended⟩ := front_appends input w a h
  have result := front_checked input entry a
  refine ⟨suffix,extended,?_,?_⟩
  · rcases result.1 with stopped | normal
    · obtain ⟨after,snapshot,_,kept,_,_⟩ := stopped
      exact entrySafe _ _ _ kept
    · obtain ⟨after,snapshot,kept⟩ := normal
      exact entrySafe _ _ _ kept
  · cases performed : (runPrefix
        ((CausalJournal.front input.family input.address input.packets input.mtu).run w) a h).1 with
    | error stop => trivial
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      have result' := result.2
      change (match (runPrefix
        ((CausalJournal.front input.family input.address input.packets input.mtu).run w) a h).1 with
        | .error stop => _ | .ok ((_,v),_) => _) at result'
      rw [performed] at result'
      exact result'

theorem keepalive (pid : PeerId) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h) :
    StatePrefixPreserves (Carrier debts locals) Safe (CausalJournal.keepalivePrepare pid) := by
  intro w a h before
  obtain ⟨ledger,entry⟩ := before
  have appends : StateAppends (CausalJournal.keepalivePrepare pid) :=
    (StateAppends.lift _).receiptWGObserved _
  obtain ⟨suffix,extended⟩ := appends w a h
  cases performed : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h with
  | mk outcome last =>
    have contract := keepalive_checked pid entry a
    rw [performed] at contract
    change runPrefix ((CausalJournal.keepalivePrepare pid).run w) a h = _ at performed
    rw [performed] at extended ⊢
    cases outcome with
    | error stop =>
      exact ⟨suffix,extended,entrySafe _ _ _ contract.2.2.1,True.intro⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      obtain ⟨after,kept,_,_⟩ := contract.2.2.2
      exact ⟨suffix,extended,entrySafe _ _ _ kept,after,kept⟩

theorem release (peer : Option PeerId) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h) :
    StatePrefixPreserves (Carrier debts locals) Safe (CausalJournal.peerRelease peer) := by
  intro w a h before
  obtain ⟨ledger,entry⟩ := before
  exact OriginalRelease.checked peer Safe entrySafe w a h entry

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Source
