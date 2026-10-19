import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerSpineFrames

/-! Internal RX phases retain the exact holder account while a cell is
unpublished, selected or paid. StableRx belongs to the remaining queued
carriers; it must not be asserted for a selected or paid cell. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Queues Queues.RxCredits DurableHolders

structure Phased (holders : DurableHolders) (carriers : RxCredits.Ledger)
    (loans : Reservations) (w : WGWorld) : Prop where
  funded : holders.Funded carriers loans w
  upper : Upper holders carriers loans w

theorem Account.phased (account : Account holders carriers loans w) :
    Phased holders carriers loans w := ⟨account.funded,account.upper⟩

theorem Phased.boundary (account : Phased holders carriers loans w)
    (stable : StableRx carriers w) : Account holders carriers loans w :=
  ⟨account.funded,account.upper,stable⟩

theorem Upper.carriers_perm (upper : Upper holders carriers loans w)
    (same : carriers.Perm other) : Upper holders other loans w := by
  intro owner
  have eq : charges carriers owner = charges other owner := (same.filter _).length_eq
  simpa only [demand,←eq] using upper owner

theorem Upper.loan_to_carrier {c : RxCredits.Carrier}
    (upper : Upper holders carriers (c.owner :: loans) w)
    (charged : c.phase.charged = true) : Upper holders (c :: carriers) loans w := by
  intro owner
  have old := upper owner
  by_cases eq : c.owner = owner <;>
    simp [demand,charged,eq] at old ⊢ <;> omega

theorem Upper.paid_remove {c : RxCredits.Carrier}
    (upper : Upper holders (paid c :: carriers) loans w) : Upper holders carriers loans w := by
  intro owner
  simpa only [demand,charges_paid] using upper owner

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
