import Leanux.Proofs.WG.RetirementSecurity.HolderDumpCursor

/-! Full native dump chunks conserve key credit through their original
serializer and cursor replacement. Source cursor alignment is derived from
the actual read-only walk, including split and cancelled chunks. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDump
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders NetlinkDump

theorem finish_keys (seq : Nat) (ctx : DumpCtx) (old : Option Owner)
    (nextCursor : Option PeerId) (skb : NlSkb) (flags : Nat)
    (device : List (String×Lean.Json)) (done : Bool) (peers : Option (Array PeerDumpAttrs))
    (cursor : ctx.nextPeer=old.map Owner.slot)
    (funded : ClearWork.Inv carriers (old.toList ++ (holders.owners ++ loans)) w)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((DumpReservation.finishSource seq ctx nextCursor skb flags device done peers).run w).run a=
      .ok ((result,v),b)) : HolderAccount temporary v := by
  unfold DumpReservation.finishSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,paid,ap,exchange,rest⟩ := run
  cases u
  have after := replace_keys ctx old nextCursor done cursor funded keys anchors a ap exchange
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨flag,checked,ac,decision,rest⟩ := rest
  obtain ⟨flagEq,same⟩ := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g=>g=paid) .dumpRetErr false) paid ap flag checked ac rfl decision
  subst flag
  subst checked
  simp only [Bool.false_eq_true,ite_false] at rest
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨flag,checked,ad,decision,rest⟩ := rest
  obtain ⟨flagEq,same⟩ := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g=>g=paid) .dumpDone done) paid ac flag checked ad rfl decision
  subst flag
  subst checked
  cases done <;> simp only [Bool.false_eq_true,ite_false,ite_true] at rest
  all_goals
    change Except.ok ((_,paid),ad)=Except.ok ((result,v),b) at rest
    cases rest
    exact after

theorem tail_keys (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (device : List (String×Lean.Json)) (old : Option Owner)
    (cursor : ctx.nextPeer=old.map Owner.slot)
    (funded : ClearWork.Inv carriers (old.toList ++ (holders.owners ++ loans)) w)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((deviceDumpTailSource d ctx skb flags device).run w).run a=.ok ((result,v),b)) :
    HolderAccount temporary v := by
  obtain ⟨walk,u,ac,walking,finish⟩ := DumpReservation.tail_cut d ctx skb flags device a b run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (DumpReservation.walk_frame d ctx skb) w a walk u ac walking
  change u=w at same
  subst u
  have selected := ((hoare_iff_run_ambient _ _ _).mp (DumpReservation.walk_cursor d ctx skb)
    w a walk w ac True.intro walking).trans cursor
  exact finish_keys _ _ old _ _ _ _ _ _ selected funded keys anchors ac b finish

theorem anchors_store (entry : SlotPeerReferences holders loans w)
    (same : wgStoreView v=wgStoreView w) : SlotPeerReferences holders loans v := by
  have device : v.dev=w.dev := congrArg WGStoreView.dev same
  simpa only [SlotPeerReferences,device] using entry

theorem chunk_keys (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) (old : Option Owner)
    (cursor : ctx.nextPeer=old.map Owner.slot)
    (funded : ClearWork.Inv carriers (old.toList ++ (holders.owners ++ loans)) w)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((wgGetDeviceDump ctx seq skb).run w).run a=.ok ((result,v),b)) : HolderAccount temporary v := by
  rw [wgGetDeviceDump_source,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,read,ar,getter,rest⟩ := run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp getDev_sameWGStore w a d read ar getter
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨⟨s,flags,attrs⟩,header,ah,headerRun,tailRun⟩ := rest
  have headerSame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (deviceDumpHeader_sameWGStore d ctx seq skb) read ar (s,flags,attrs) header ah headerRun
  have both := headerSame.trans same
  exact tail_keys d ctx s flags attrs old cursor
    ⟨funded.1.kernel both,funded.2.kernel both⟩ (HolderPoll.keys_store keys both)
    (anchors_store anchors both) ah b tailRun

theorem finish_anchors (seq : Nat) (ctx : DumpCtx) (next : Option PeerId) (skb : NlSkb)
    (flags : Nat) (attrs : List (String×Lean.Json)) (done : Bool) (peers : Option (Array PeerDumpAttrs)) :
    Preserves (SlotPeerReferences holders loans)
      (DumpReservation.finishSource seq ctx next skb flags attrs done peers) := by
  unfold DumpReservation.finishSource
  simp (config:={zeta:=false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head DumpReservation.replaceSource; exact replace_anchors _ _ _)
    | slot_anchor_step

theorem tail_anchors (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String×Lean.Json)) :
    Preserves (SlotPeerReferences holders loans) (deviceDumpTailSource d ctx skb flags attrs) := by
  rw [DumpReservation.tail_factor]
  exact preserves_bind ((DumpReservation.walk_frame d ctx skb).wp (SlotPeerReferences holders loans))
    (fun r=>finish_anchors _ _ _ _ _ _ _ _)

theorem chunk_anchors (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) :
    Preserves (SlotPeerReferences holders loans) (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  exact preserves_bind (SlotAnchors.store getDev_sameWGStore) (fun d=>
    preserves_bind (SlotAnchors.store (deviceDumpHeader_sameWGStore d ctx seq skb))
      (fun r=>tail_anchors _ _ _ _ _))

end Leanux.Proofs.WG.RetirementSecurity.HolderDump
