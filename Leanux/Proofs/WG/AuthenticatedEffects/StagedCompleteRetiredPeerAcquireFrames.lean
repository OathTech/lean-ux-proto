import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPhases
import Leanux.Proofs.WG.Queues.HolderAdmission

/-! Native index acquisition preserves the same holder list and adds the
single owner loan justified by the actual source increment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem Upper.loan (upper : Upper holders carriers loans w) (loan : Loan w (some pid) v) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Upper holders carriers (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  obtain ⟨d,p,device,stored,positive,view,_⟩ := loan
  refine ⟨d,p,device,stored,positive,?_⟩
  intro owner
  have equation := (balance_view (o := owner) view).trans (credit_balance device stored owner)
  have old := upper owner
  by_cases eq : owner = ⟨d.ifindex,pid,p.internalId⟩
  · simp [demand,eq] at *
    omega
  · simp [demand,eq,Ne.symm eq] at *
    omega

/-- The lower and upper source results are unified by the actual entry
Device and peer cell, so their owner stamps cannot differ. -/
theorem Account.lookup (account : Account holders carriers loans w)
    (a b : Ambient)
    (run : ((indexLookup kinds index).run w).run a = .ok ((some (owner,pid),v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Account holders carriers (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  have loan := (hoare_iff_run_ambient _ _ _).mp (indexLookup_loan kinds index w)
    w a _ v b rfl run
  obtain ⟨d,p,device,stored,positive,upper⟩ := account.upper.loan loan
  obtain ⟨other,q,otherDevice,otherStored,_,funded⟩ := lookup_carriers account.funded.carriers a b run
  have eq := Option.some.inj (device.symm.trans otherDevice)
  subst other
  have eq := Option.some.inj (stored.symm.trans otherStored)
  subst q
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderAdmission.index_frame kinds index w)
    w a _ v b (Frame.refl w) run
  have stable := account.stable.view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (stable_indexLookup kinds index) w a _ v b run)
  exact ⟨d,p,device,stored,positive,⟨account.funded.aligned.frame frame,
    WorkReservations.carrier_loans_perm funded List.perm_middle.symm⟩,upper,stable⟩

/-- A failed nullable lookup adds no peer loan. Its possible owner-word
write is retained by the original key-effect proof. -/
theorem Account.lookup_none (account : Account holders carriers loans w)
    (a b : Ambient)
    (run : ((indexLookup kinds index).run w).run a = .ok ((none,v),b)) :
    Account holders carriers loans v := by
  have loan := (hoare_iff_run_ambient _ _ _).mp (indexLookup_loan kinds index w)
    w a _ v b rfl run
  change peerView v = peerView w ∧ rxView v = rxView w at loan
  have keys := (KeyEffects.iff_run_ambient _ _).mp
    (indexLookup_keyEffect kinds index) w a _ v b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderAdmission.index_frame kinds index w)
    w a _ v b (Frame.refl w) run
  refine ⟨⟨account.funded.aligned.frame frame,?_,?_,?_,?_,?_⟩,
    account.upper.peer_view loan.1,account.stable.view
      ((ProjectedAction.iff_run_ambient _ _ _).mp (stable_indexLookup kinds index) w a _ v b run)⟩
  · exact inventory_view account.funded.carriers.inventory loan.2
  · exact queueOwners_view account.funded.carriers.queues loan.1
  · exact protected_view account.funded.carriers.funded loan.1
  · exact keys.rxCompatible loan.2 account.funded.carriers.keys.1
  · exact keys.currentsCompatible account.funded.carriers.keys.2 (fun _ _ h => h.elim)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
