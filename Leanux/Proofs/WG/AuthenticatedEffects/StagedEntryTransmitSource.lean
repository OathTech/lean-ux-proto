import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTransmitSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryContract

/-! Source-complete local transmit contracts. Allocation derives the pending
batch, and the real creation callback discharges it; stopped creation retains
its explicit source frontier. These local certificates are not a substitute
for the initialized historical conservation claim. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Transmit
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
open AllocatedObligation CausalJournal

/-- The local history certificate distinguishes ordinary entry, a live
staging selection, and the exact creation frontier reached before Stop. -/
inductive Accounted (debts : List CleanupDebt) (locals : List TxLocalBatch) : List Event → Prop where
  | entry (ledger h w) (kept : Inv h ledger debts locals w) : Accounted debts locals h
  | selected (ledger generation pid peer position h)
      (kept : SoundHeld.Active ledger debts generation pid peer position h) : Accounted debts locals h
  | creation (ledger pid items w h stop last)
      (cut : CreateEntry.CreatedStop ledger debts locals pid items w h stop last) : Accounted debts locals last

theorem staging (pid : PeerId) : StatePrefixPreserves (Source.Carrier debts locals)
    (Accounted debts locals) (Driver.stagingObserved hooks pid) := by
  apply EntrySource.staging pid (Accounted debts locals)
    (fun ledger h w entry => .entry ledger h w entry)
    (fun ledger generation peer position h active => .selected ledger generation pid peer position h active)
  intro ledger items
  exact CreateEntry.checked ledger debts locals pid items (Accounted debts locals)
    (fun w h stop last cut => .creation ledger pid items w h stop last cut)
    (fun after h w entry => .entry after h w entry)
    (Source.Carrier debts locals) (fun after _ _ _ entry => ⟨after,entry⟩)

theorem keepalive (pid : PeerId) : StatePrefixPreserves (Source.Carrier debts locals)
    (Accounted debts locals) (Driver.keepaliveObserved hooks pid) :=
  EntrySource.keepalive pid (Accounted debts locals)
    (fun ledger h w entry => .entry ledger h w entry) (staging pid)

/-- Actual front, native allocation, creation and owner release transport the
complete entry bundle, with no assumed creation or queued-initiation callback. -/
theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StatePrefixPreserves (Source.Carrier debts locals) (Accounted debts locals)
      (Driver.transmitObserved hooks family addr packets mtu) :=
  EntrySource.transmit family addr packets mtu (Accounted debts locals)
    (fun ledger h w entry => .entry ledger h w entry) staging

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Transmit
