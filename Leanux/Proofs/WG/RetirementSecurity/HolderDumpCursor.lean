import Leanux.Proofs.WG.RetirementSecurity.HolderOuterControls
import Leanux.Proofs.WG.Queues.DumpCallers

/-! A native dump cursor is a peer loan separate from every key-slot anchor.
Its actual acquisition and payment preserve the exact key-holder account,
including when old and replacement cursors name the same peer. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDump
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders NetlinkDump

theorem anchor_extend (before : SlotPeerReferences holders loans w) (o : Owner) :
    SlotPeerReferences holders (o::loans) w := by
  intro d pid p device stored slots
  have member := before d pid p device stored slots
  simp only [List.mem_append,List.mem_cons] at member ⊢
  exact member.elim Or.inl (fun h=>Or.inr (Or.inr h))

theorem put_keys (old : Option Owner)
    (funded : ClearWork.Inv carriers (old.toList ++ (holders.owners ++ loans)) w)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((peerPut (old.map Owner.slot)).run w).run a=.ok (((),v),b)) :
    HolderAccount temporary v := by
  cases old with
  | none=>
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact keys
  | some o=>
    have credit : CarrierState carriers (holders.owners ++ o::loans) w :=
      WorkReservations.carrier_loans_perm funded.1
        (by simpa using (List.perm_middle.symm : (o::holders.owners++loans).Perm (holders.owners++o::loans)))
    exact keys.peer_put (selected_loan_peer_release_funded credit anchors).ready a b run

theorem done_keys (ctx : DumpCtx) (old : Option Owner)
    (cursor : ctx.nextPeer=old.map Owner.slot)
    (funded : ClearWork.Inv carriers (old.toList ++ (holders.owners ++ loans)) w)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((wgGetDeviceDone ctx).run w).run a=.ok (((),v),b)) : HolderAccount temporary v := by
  unfold wgGetDeviceDone at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨flag,checked,ac,decision,payment⟩ := run
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .getDoneHasWg ctx.hasWg) (fun g=>g=w))
    w a flag checked ac rfl decision
  subst checked
  exact put_keys old funded keys anchors ac b (cursor ▸ payment)

theorem get_anchors (pid : PeerId) : Preserves (SlotPeerReferences holders loans) (peerGet pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  obtain ⟨d,p,device,stored,_,same⟩ := peerGet_loan pid w v a b run
  have kept := before.replace device stored (q:={p with refcount:=p.refcount+1}) rfl (fun h=>h)
  have actual : v.dev=(replacePeer w d pid {p with refcount:=p.refcount+1}).dev := congrArg WGStoreView.dev same
  simpa only [SlotPeerReferences,actual] using kept

theorem replace_keys (ctx : DumpCtx) (old : Option Owner) (nextCursor : Option PeerId) (done : Bool)
    (cursor : ctx.nextPeer=old.map Owner.slot)
    (funded : ClearWork.Inv carriers (old.toList ++ (holders.owners ++ loans)) w)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((DumpReservation.replaceSource ctx nextCursor done).run w).run a=.ok (((),v),b)) :
    HolderAccount temporary v := by
  unfold DumpReservation.replaceSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨flag,checked,ac,decision,rest⟩ := run
  obtain ⟨rfl,rfl⟩ := (pinned_const _private.Leanux.Proofs.WG.Queues.DumpReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.DumpReservation.guard_normal)
    done nextCursor a ac decision
  cases done with
  | true=>
    simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false] at rest
    exact put_keys old funded keys anchors ac b (cursor ▸ rest)
  | false=>
    cases nextCursor with
    | none=>
      simp only [Bool.not_false,Option.isSome_none,Bool.and_false,Bool.false_eq_true,ite_false] at rest
      exact put_keys old funded keys anchors ac b (cursor ▸ rest)
    | some pid=>
      simp only [Bool.not_false,Option.isSome_some,Bool.true_and,ite_true,MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨u,got,ag,acquire,payment⟩ := rest
      cases u
      obtain ⟨d,p,_,_,_,after⟩ := ClearWork.acquire funded ac ag acquire
      let o : Owner := ⟨d.ifindex,pid,p.internalId⟩
      have reordered : ClearWork.Inv carriers (old.toList ++ (holders.owners ++ o::loans)) got := by
        refine ⟨WorkReservations.carrier_loans_perm after.1 ?_,after.2⟩
        simpa only [List.append_assoc] using
          (List.perm_middle.symm : (o::(old.toList++holders.owners)++loans).Perm ((old.toList++holders.owners)++o::loans))
      have account := keys.points ((ProjectedAction.iff_run_ambient _ _ _).mp (peerGet_ownership pid) _ ac () got ag acquire)
      have retained := (hoare_iff_run_ambient _ _ _).mp (get_anchors pid) _ ac () got ag anchors acquire
      exact put_keys old reordered account (anchor_extend retained o) ag b (cursor ▸ payment)

theorem done_anchors (ctx : DumpCtx) : Preserves (SlotPeerReferences holders loans) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  exact preserves_bind (hoare_liftAmbient (AmbientM.branch .getDoneHasWg ctx.hasWg) _)
    (fun _=>SlotAnchors.peer_put _)

theorem replace_anchors (ctx : DumpCtx) (next : Option PeerId) (done : Bool) :
    Preserves (SlotPeerReferences holders loans) (DumpReservation.replaceSource ctx next done) := by
  unfold DumpReservation.replaceSource WG.andM
  simp (config:={zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerGet; exact get_anchors _)
    | slot_anchor_step

end Leanux.Proofs.WG.RetirementSecurity.HolderDump
