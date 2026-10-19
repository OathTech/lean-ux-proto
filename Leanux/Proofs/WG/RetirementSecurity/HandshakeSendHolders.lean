import Leanux.Proofs.WG.RetirementSecurity.HolderHandshakeFrames
import Leanux.Proofs.WG.RetirementSecurity.RemovalPeerFunding

/-! A native handshake-send worker pays its actual peer work occurrence.
The separately anchored base/caller occurrence prevents erasing uncleared
key slots. Peer funding protects peer release; it is never counted as key credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem selected_loan_peer_release_funded
    (funded : CarrierState carriers (holders.owners ++ o :: loans) w)
    (anchors : SlotPeerReferences holders loans w) : PeerReleaseFunded o.slot w := by
  have present : 0 < demand carriers (holders.owners ++ o :: loans) o := by
    simp only [demand,List.count_append,List.count_cons,beq_self_eq_true,ite_true]
    omega
  obtain ⟨q,resident,budget⟩ := protected_resident funded.funded present
  obtain ⟨d,device,epoch,stored,stamp⟩ := resident_fields resident
  intro p found
  have same : q = p := Option.some.inj ((show peerAt w o.slot = some q by
    simp [peerAt,device,stored]).symm.trans found)
  subst q
  have owner : o = ⟨d.ifindex,o.slot,p.internalId⟩ := by
    cases o
    simp_all
  refine ⟨by omega,?_⟩
  intro final
  have noSlots : ¬ (p.keypairNext ≠ none ∨ p.keypairPrevious ≠ none ∨ p.keypairCurrent ≠ none) := by
    intro slots
    have anchored := anchors d o.slot p device stored slots
    rw [← owner] at anchored
    have extra := List.count_pos_iff.mpr anchored
    simp only [List.count_append] at extra
    simp only [demand,DurableHolders.owners,List.count_append,List.count_cons,beq_self_eq_true,ite_true] at budget
    omega
  refine ⟨?_,?_,?_⟩
  · by_cases h : p.keypairNext = none
    · exact h
    · exact False.elim (noSlots (Or.inl h))
  · by_cases h : p.keypairPrevious = none
    · exact h
    · exact False.elim (noSlots (Or.inr (Or.inl h)))
  · by_cases h : p.keypairCurrent = none
    · exact h
    · exact False.elim (noSlots (Or.inr (Or.inr h)))


namespace HolderHandshake

theorem initiation_peers (pid : PeerId) : SameView peerView (sendHandshakeInitiation pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.sendHandshakeInitiation_view) pid)
    w a result v b run
  have carrier := ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) v).trans
    ((congrArg (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrierOf) same).trans
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) w).symm)
  exact congrArg Prod.fst carrier

end HolderHandshake

/-- The terminal peer put is safe for the separate key ledger because its
real selected work reference is funded and every published key slot retains
an independent base/caller reference. The native initiation frame supplies
both exact key-holder fields and actual peer-refcount continuity. -/
theorem HolderAccount.handshake_send_worker (account : HolderAccount temporary w)
    (funded : CarrierState carriers (holders.owners ++ o :: loans) w)
    (stable : StableRx carriers w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((handshakeSendWorker o.slot).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  rw [handshakeSendWorker,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,u,c,sendRun,putRun⟩ := run
  cases ignored
  have points := (ProjectedAction.iff_run_ambient _ _ _).mp
    (HolderHandshake.initiation_points o.slot) w a () u c sendRun
  have peers := (ProjectedAction.iff_run_ambient _ _ _).mp
    (HolderHandshake.initiation_peers o.slot) w a () u c sendRun
  have after := (hoare_iff_run_ambient _ _ _).mp (SendWork.initiation_preserves o.slot)
    w a () u c ⟨funded,stable⟩ sendRun
  have retainedAnchors := anchors.transport peers points (List.Perm.refl _)
  exact (account.points points).peer_put
    (selected_loan_peer_release_funded after.1 retainedAnchors).ready c b putRun

end Leanux.Proofs.WG.RetirementSecurity
