import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerSpineFrames
import Leanux.Proofs.WG.RetirementSecurity.HolderBulkRemoval

/-! Bulk base detachment keeps every saved occurrence as an explicit loan.
The actual trie clear and mark-dead pass do not pay any reference; payment
belongs to the later original after-dead source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

/-- Move all base occurrences to the caller without changing the budget. -/
theorem Upper.detach_all (upper : Upper holders carriers loans w) :
    Upper (holders.withoutBase []) carriers (holders.base ++ loans) w := by
  apply upper.relabel
  apply List.perm_iff_count.mpr
  intro owner
  simp only [withoutBase,owners,List.count_append,List.count_nil]
  omega

theorem saved_entry_peers : SameView peerView BaseRemoval.entry := by
  unfold BaseRemoval.entry
  exact (BaseRemoval.allowedipsFree_view.factor (fun s => s.1.1.1)).bind
    (fun _ => (getDev_sameWGStore.of_factor (fun s => peerView {dev := s.dev}) _ (fun _ => rfl)).bind
      (fun _ => SameView.pure _ _))

theorem Account.saved_entry (account : Account holders carriers loans w) (a b : Ambient)
    (run : (BaseRemoval.entry.run w).run a = .ok ((dead,v),b)) :
    dead = holders.base.map Owner.slot ∧ Account holders carriers loans v := by
  obtain ⟨saved,funded,stable⟩ := saved_entry_funded account.funded account.stable a b run
  exact ⟨saved,funded,account.upper.peer_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp saved_entry_peers w a dead v b run),stable⟩

/-- The source-selected first pass retains the same actual base list as loans;
no uniqueness of slots or immediate peer destruction is assumed. -/
theorem Account.saved_make_dead (account : Account holders carriers loans w) (a b : Ambient)
    (run : (((for pid in holders.base.map Owner.slot do
      _ ← branch .peerRemoveAllIter1 true
      peerMakeDead pid) : WG.M Unit).run w).run a = .ok (((),v),b)) :
    Account (holders.withoutBase []) carriers (holders.base ++ loans) v := by
  obtain ⟨funded,stable⟩ := saved_makeDead_funded account.funded account.stable a b run
  have effect := (pinned_const
    _private.Leanux.Proofs.WG.Queues.HolderBaseRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.mark_saved_effect)
    (holders.base.map Owner.slot) w v a b run
  exact ⟨funded,(account.upper.peer_view (congrArg (fun s => s.1.1) effect.1)).detach_all,stable⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
