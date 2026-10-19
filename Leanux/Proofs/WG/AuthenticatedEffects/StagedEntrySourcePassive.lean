import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourceContracts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPassive

/-! Sequential entry accounting can choose a successor ledger only at a
settlement contract. Fixed-ledger maintenance embeds without losing its
failure-side accounted witness. The enclosing history condition stays explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SourcePassive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal

abbrev Checked (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (Safe : List Event → Prop) (action : WGPrefix Event α) : Prop :=
  StatePrefixPreserves (Source.Carrier debts locals) Safe action

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)

include entrySafe in
theorem pure_checked (value : α) : Checked debts locals Safe (pure value) :=
  StatePrefixEnsures.pure value
    (fun h w _ before => by obtain ⟨ledger,entry⟩ := before; exact entrySafe ledger h w entry)
    (fun _ _ _ entry => entry)

theorem bind_checked {action : WGPrefix Event α} {next : α → WGPrefix Event β}
    (head : Checked debts locals Safe action)
    (tail : ∀ x, Checked debts locals Safe (next x)) :
    Checked debts locals Safe (action >>= next) := StatePrefixEnsures.bind head tail

include entrySafe in
theorem fixed {action : WGPrefix Event α}
    (checked : ∀ ledger, Passive.Checked ledger debts locals action) :
    Checked debts locals Safe action := by
  intro w a h before
  obtain ⟨ledger,entry⟩ := before
  obtain ⟨suffix,extended,safe,kept⟩ := checked ledger w a h entry
  refine ⟨suffix,extended,?_,?_⟩
  · obtain ⟨cut,accounted⟩ := safe
    exact entrySafe ledger _ cut accounted
  · cases performed : (runPrefix (action.run w) a h).1 with
    | error stop => trivial
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      rw [performed] at kept
      exact ⟨ledger,kept⟩

include entrySafe in
theorem native (action : WG.M α) (frame : SameView StagedEntry.view action) :
    Checked debts locals Safe (liftWGPrefix action) :=
  fixed Safe entrySafe (fun _ => Passive.native action frame)

include entrySafe in
theorem ambient (action : AmbientM α) :
    Checked debts locals Safe (liftWGPrefix (monadLift action : WG.M α)) :=
  fixed Safe entrySafe (fun _ => Passive.ambient action)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SourcePassive
