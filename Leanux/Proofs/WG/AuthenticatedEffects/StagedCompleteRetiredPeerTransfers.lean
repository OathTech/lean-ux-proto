import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerFrames
import Leanux.Proofs.WG.Queues.HolderBaseRetirement
import Leanux.Proofs.WG.Queues.HolderCreation

/-! Reassigning the same physical peer-reference occurrences cannot create
upper-account slack. Every permutation below uses C1's actual holder choices. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Queues.RxCredits
open DurableHolders
variable {holders next : DurableHolders} {carriers : RxCredits.Ledger}
  {loans rest : Reservations} {w : WGWorld}

theorem Upper.relabel (upper : Upper holders carriers loans w)
    (same : (holders.owners ++ loans).Perm (next.owners ++ rest)) :
    Upper next carriers rest w := by
  intro owner
  have count := List.Perm.count_eq same owner
  simpa only [demand,← count] using upper owner

/-- Publication moves the allocation's original loan into the base holder;
it does not increase the total reference budget. -/
theorem Upper.publish (upper : Upper holders carriers (owner :: loans) w) :
    Upper (HolderCreation.addBase holders owner) carriers loans w := by
  apply upper.relabel
  exact (List.perm_middle.trans ((HolderCreation.addBase_owners holders owner).append_right loans).symm)

/-- Detachment keeps all matching occurrences as explicit caller loans,
including repeated slots. No distinctness assumption is introduced. -/
theorem Upper.detach (upper : Upper holders carriers loans w) (pid : PeerId) :
    Upper (holders.withoutBase (BaseRemoval.live holders.base pid)) carriers
      (BaseRemoval.detached holders.base pid ++ loans) w := by
  apply upper.relabel
  apply List.perm_iff_count.mpr
  intro owner
  have count := List.Perm.count_eq (BaseRemoval.partition holders.base pid) owner
  simp only [List.count_append] at count
  simp only [withoutBase,owners,List.count_append]
  omega

theorem Upper.take_clear (upper : Upper holders carriers loans w)
    (selected : WorkReservations.Selected holders.clear pid owner rest) :
    Upper (holders.withoutClear rest) carriers (owner :: loans) w := by
  apply upper.relabel
  apply List.perm_iff_count.mpr
  intro other
  have count := List.Perm.count_eq selected.perm other
  simp only [List.count_cons] at count
  simp only [withoutClear,owners,List.count_append,List.count_cons]
  omega

theorem Upper.take_send (upper : Upper holders carriers loans w)
    (selected : WorkReservations.Selected holders.send pid owner rest) :
    Upper (holders.withoutSend rest) carriers (owner :: loans) w := by
  apply upper.relabel
  apply List.perm_iff_count.mpr
  intro other
  have count := List.Perm.count_eq selected.perm other
  simp only [List.count_cons] at count
  simp only [withoutSend,owners,List.count_append,List.count_cons]
  omega

/-- A source-local strengthening of C1's account. Both bounds refer to the
same holder list, RX carrier list and transient loans. -/
structure Account (holders : DurableHolders) (carriers : RxCredits.Ledger)
    (loans : Reservations) (w : WGWorld) : Prop where
  funded : holders.Funded carriers loans w
  upper : Upper holders carriers loans w
  stable : StableRx carriers w

/-- Existential packaging is allowed only after the same concrete account is
proved. C1's lower-only Boundary has no converse conversion. -/
def ExactBoundary (carriers : RxCredits.Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  ∃ holders, Account holders carriers loans w

theorem Account.exact (account : Account holders carriers loans w) (owner : Owner) :
    balance w owner = demand carriers (holders.owners ++ loans) owner :=
  account.upper.exact account.funded owner

theorem Account.initial (net bare : Bool) : Account {} [] [] (Runner.initialWG net bare) := by
  refine ⟨⟨aligned_initial net bare,?_⟩,Upper.initial net bare,stable_initial net bare _ rfl⟩
  exact carrier_initial net bare _ rfl

theorem ExactBoundary.lower (account : ExactBoundary carriers loans w) : Boundary carriers loans w := by
  obtain ⟨holders,account⟩ := account
  exact ⟨holders,account.funded,account.stable⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
