import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAccounting

/-! Native peer-payment frames for the upper half of the same C1 holder
account. Final and nonfinal releases are both covered on actual normal return. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Queues.RxCredits
variable {holders : DurableHolders} {carriers : RxCredits.Ledger}
  {loans : Reservations} {w v : WGWorld} {a b : Ambient} {owner : Owner} {p : Peer}

theorem Upper.peer_view (upper : Upper holders carriers loans w)
    (same : peerView v = peerView w) : Upper holders carriers loans v := by
  intro owner
  rw [balance_view same]
  exact upper owner

/-- Payment consumes exactly the supplied transient occurrence. Actual source
success establishes positivity; no nonfinal-only assumption excludes retirement. -/
theorem Upper.payment (upper : Upper holders carriers (owner :: loans) w)
    (found : resident w owner = some p)
    (run : ((peerPut (some owner.slot)).run w).run a = .ok (((),v),b)) :
    Upper holders carriers loans v := by
  obtain ⟨d,device,epoch,peer,stamp⟩ := resident_fields found
  obtain ⟨positive,same,_⟩ := peerPut_effect owner.slot w v d p a b device peer run
  have identity : owner = ⟨d.ifindex,owner.slot,p.internalId⟩ := by
    cases owner
    simp_all
  intro other
  have equation := (balance_view (o := other) same).trans (payment_balance device peer positive other)
  rw [← identity] at equation
  have old := upper other
  by_cases eq : other = owner
  · subst other
    simp only [ite_true] at equation
    simp only [demand,List.count_append,List.count_cons_self] at old ⊢
    omega
  · rw [ite_eq_right eq] at equation
    simp only [demand,List.count_append,List.count_cons_of_ne (Ne.symm eq)] at old ⊢
    omega

/-- The native RX payment changes only that carrier's charge to paid. The
physical cell remains a separate cleanup obligation until its actual free. -/
theorem Upper.receive_payment {carrier : Carrier}
    (upper : Upper holders (carrier :: carriers) loans w)
    (selected : carrier.phase = .selected) (found : resident w carrier.owner = some p)
    (run : ((peerPut (some carrier.owner.slot)).run w).run a = .ok (((),v),b)) :
    Upper holders (paid carrier :: carriers) loans v := by
  obtain ⟨d,device,epoch,peer,stamp⟩ := resident_fields found
  obtain ⟨positive,same,_⟩ := peerPut_effect carrier.owner.slot w v d p a b device peer run
  have identity : carrier.owner = ⟨d.ifindex,carrier.owner.slot,p.internalId⟩ := by
    simp only [epoch,stamp]
  intro other
  have equation := (balance_view (o := other) same).trans (payment_balance device peer positive other)
  rw [← identity] at equation
  have old := upper other
  by_cases eq : other = carrier.owner
  · subst other
    simp only [ite_true] at equation
    simp only [demand,charges_paid] at old ⊢
    have charge : charges (carrier :: carriers) carrier.owner = 1 + charges carriers carrier.owner := by
      simp [selected,Phase.charged]
    rw [charge] at old
    omega
  · rw [ite_eq_right eq] at equation
    simp only [demand,charges_paid] at old ⊢
    have charge : charges (carrier :: carriers) other = charges carriers other := by
      simp [Ne.symm eq]
    rw [charge] at old
    omega

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
