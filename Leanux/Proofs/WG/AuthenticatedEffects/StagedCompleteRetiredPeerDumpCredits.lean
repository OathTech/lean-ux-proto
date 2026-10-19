import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerSpineFrames
import Leanux.Proofs.WG.Queues.DumpSockets

/-! A dump temporarily carries its old socket cursor as an explicit loan.
The exact lower and upper bounds use the same occurrence list throughout;
publication restores alignment with the actual socket cursor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders NetlinkDump
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Credits (carriers : RxCredits.Ledger) (loans : Reservations) (w : WGWorld) : Prop where
  lower : ClearWork.Inv carriers loans w
  upper : Upper {} carriers loans w

theorem Credits.perm (account : Credits carriers loans w) (same : loans.Perm next) :
    Credits carriers next w := by
  refine ⟨⟨WorkReservations.carrier_loans_perm account.lower.1 same,account.lower.2⟩,?_⟩
  apply account.upper.relabel
  simpa only [DurableHolders.owners,List.map_nil,Option.toList_none,List.nil_append,List.append_nil] using same

theorem Credits.store (account : Credits carriers loans w) (same : wgStoreView v = wgStoreView w) :
    Credits carriers loans v := by
  have device : v.dev = w.dev := congrArg WGStoreView.dev same
  exact ⟨⟨account.lower.1.kernel same,account.lower.2.kernel same⟩,
    account.upper.peer_view (by simp only [peerView,device])⟩

theorem Credits.acquire (account : Credits carriers loans w) (pid : PeerId) (a b : Ambient)
    (run : ((peerGet pid).run w).run a = .ok (((),v),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      Credits carriers (⟨d.ifindex,pid,p.internalId⟩ :: loans) v := by
  obtain ⟨d,p,device,resident,positive,lower⟩ := ClearWork.acquire account.lower a b run
  obtain ⟨d',p',device',resident',_,step⟩ := peerGet_handoff a b run
  have deq : d' = d := Option.some.inj (device'.symm.trans device)
  subst d'
  have peq : p' = p := Option.some.inj (resident'.symm.trans resident)
  subst p'
  refine ⟨d,p,device,resident,positive,lower,?_⟩
  intro other
  have before := account.upper other
  have equation := step.count other
  simp only [demand,DurableHolders.owners,HandoffDelta.owners,List.map_nil,Option.toList_none,
    List.count_cons,List.count_nil,List.nil_append,List.append_nil] at before equation ⊢
  omega

theorem Credits.payment (account : Credits carriers (owner :: loans) w) (a b : Ambient)
    (run : ((peerPut (some owner.slot)).run w).run a = .ok (((),v),b)) :
    Credits carriers loans v := by
  have positive : 0 < demand carriers (owner :: loans) owner := by simp [demand]; omega
  obtain ⟨p,found,_⟩ := protected_resident account.lower.1.funded positive
  exact ⟨reservation_payment_stable account.lower.1 account.lower.2 a b run,
    account.upper.payment found run⟩

theorem Credits.put (old : Option Owner) (account : Credits carriers (old.toList ++ loans) w)
    (a b : Ambient) (run : ((peerPut (old.map Owner.slot)).run w).run a = .ok (((),v),b)) :
    Credits carriers loans v := by
  cases old with
  | none =>
    simp only [Option.map_none,Option.toList_none,List.nil_append] at account run
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact account
  | some owner => exact account.payment a b run

theorem cursor_input (account : Account holders carriers loans w) (fd : Nat) :
    Credits carriers ((holders.cursorAt fd).toList ++ outsideCursor holders fd loans) w := by
  refine ⟨DurableHolders.cursor_input account.funded account.stable fd,?_⟩
  apply account.upper.relabel
  simpa only [withCursor_current,DurableHolders.owners,List.map_nil,Option.toList_none,List.nil_append,List.append_nil] using
    cursor_owners_perm holders fd (holders.cursorAt fd) loans

theorem cursor_publish (aligned : holders.Aligned w) (fd : Nat) (sock : NlSock) (next : Option Owner)
    (cursor : next.map Owner.slot = activeCursor sock)
    (account : Credits carriers (next.toList ++ outsideCursor holders fd loans) w) :
    Account (holders.withCursor fd next) carriers loans (writeSocket fd sock w) := by
  obtain ⟨funded,stable⟩ := DurableHolders.cursor_publish aligned fd sock next cursor account.lower
  refine ⟨funded,?_,stable⟩
  have peer : peerView (writeSocket fd sock w) = peerView w := by unfold writeSocket; split <;> rfl
  apply (account.upper.peer_view peer).relabel
  simpa only [DurableHolders.owners,List.map_nil,Option.toList_none,List.nil_append,List.append_nil] using
    (cursor_owners_perm holders fd next loans).symm

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Dump
