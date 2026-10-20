import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpCredits

/-! Literal dump cursor acquisition and payment transport the exact same
reference occurrence account. The source supplies each replacement's epoch,
slot and allocation stamp; aliasing old and new cursors is allowed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders NetlinkDump
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem done (ctx : DumpCtx) (old : Option Owner)
    (cursor : ctx.nextPeer = old.map Owner.slot)
    (account : Credits carriers (old.toList ++ loans) w) (a b : Ambient)
    (run : ((wgGetDeviceDone ctx).run w).run a = .ok (((),v),b)) : Credits carriers loans v := by
  unfold wgGetDeviceDone at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨flag,checked,ac,decision,payment⟩ := run
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .getDoneHasWg ctx.hasWg) (fun g => g = w))
    w a flag checked ac rfl decision
  subst checked
  exact account.put old ac b (cursor ▸ payment)

theorem replace (ctx : DumpCtx) (old : Option Owner) (nextCursor : Option PeerId) (finished : Bool)
    (cursor : ctx.nextPeer = old.map Owner.slot)
    (account : Credits carriers (old.toList ++ loans) w) (a b : Ambient)
    (run : ((DumpReservation.replaceSource ctx nextCursor finished).run w).run a = .ok (((),v),b)) :
    ∃ next : Option Owner,
      next.map Owner.slot = (if finished then none else nextCursor) ∧
      (∀ o, next = some o → ∃ d p, w.dev = some d ∧ d.peers[o.slot]? = some p ∧
        o = ⟨d.ifindex,o.slot,p.internalId⟩ ∧ 0 < p.refcount) ∧
      Credits carriers (next.toList ++ loans) v := by
  unfold DumpReservation.replaceSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨flag,checked,ac,decision,rest⟩ := run
  obtain ⟨rfl,rfl⟩ := (pinned_const
    _private.Leanux.Proofs.WG.Queues.DumpReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.DumpReservation.guard_normal)
    finished nextCursor a ac decision
  cases finished with
  | true =>
    simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false] at rest
    refine ⟨none,rfl,?_,account.put old ac b (cursor ▸ rest)⟩
    intro o impossible; cases impossible
  | false =>
    cases nextCursor with
    | none =>
      simp only [Bool.not_false,Option.isSome_none,Bool.and_false,Bool.false_eq_true,ite_false] at rest
      refine ⟨none,rfl,?_,account.put old ac b (cursor ▸ rest)⟩
      intro o impossible; cases impossible
    | some pid =>
      simp only [Bool.not_false,Option.isSome_some,Bool.true_and,ite_true,MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨u,got,ag,acquire,payment⟩ := rest
      cases u
      obtain ⟨d,p,device,resident,positive,acquired⟩ := account.acquire pid ac ag acquire
      let o : Owner := ⟨d.ifindex,pid,p.internalId⟩
      have reordered : Credits carriers (old.toList ++ o :: loans) got :=
        acquired.perm (by simpa [o] using
          (List.perm_middle.symm : (o :: old.toList ++ loans).Perm (old.toList ++ o :: loans)))
      refine ⟨some o,rfl,?_,reordered.put old ag b (cursor ▸ payment)⟩
      intro chosen equality
      cases equality
      exact ⟨d,p,device,resident,rfl,positive⟩

theorem finish (seq : UInt32) (ctx : DumpCtx) (old : Option Owner)
    (nextCursor : Option PeerId) (skb : NlSkb) (flags : Nat)
    (attrs : List (String × Lean.Json)) (finished : Bool) (peers : Option (Array PeerDumpAttrs))
    (cursor : ctx.nextPeer = old.map Owner.slot)
    (account : Credits carriers (old.toList ++ loans) w) (a b : Ambient)
    (run : ((DumpReservation.finishSource seq ctx nextCursor skb flags attrs finished peers).run w).run a =
      .ok ((result,v),b)) :
    ∃ next : Option Owner, result.ctx.nextPeer = next.map Owner.slot ∧
      Credits carriers (next.toList ++ loans) v := by
  unfold DumpReservation.finishSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,paid,ap,exchange,rest⟩ := run
  cases u
  obtain ⟨next,slot,_,accounted⟩ := replace ctx old nextCursor finished cursor account a ap exchange
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨flag,checked,ac,decision,rest⟩ := rest
  obtain ⟨flagEq,same⟩ := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g => g = paid) .dumpRetErr false) paid ap flag checked ac rfl decision
  subst flag
  subst checked
  simp only [Bool.false_eq_true,ite_false] at rest
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨flag,checked,ad,decision,rest⟩ := rest
  obtain ⟨flagEq,same⟩ := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g => g = paid) .dumpDone finished) paid ac flag checked ad rfl decision
  subst flag
  subst checked
  cases finished <;> simp only [Bool.false_eq_true,ite_false,ite_true] at rest
  all_goals
    change Except.ok ((_,paid),ad) = Except.ok ((result,v),b) at rest
    cases rest
    exact ⟨next,slot.symm,accounted⟩

theorem tail (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) (old : Option Owner)
    (cursor : ctx.nextPeer = old.map Owner.slot)
    (account : Credits carriers (old.toList ++ loans) w) (a b : Ambient)
    (run : ((deviceDumpTailSource d ctx skb flags attrs).run w).run a = .ok ((result,v),b)) :
    ∃ next : Option Owner, result.ctx.nextPeer = next.map Owner.slot ∧
      Credits carriers (next.toList ++ loans) v := by
  obtain ⟨walk,u,ac,walking,rest⟩ := DumpReservation.tail_cut d ctx skb flags attrs a b run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (DumpReservation.walk_frame d ctx skb) w a walk u ac walking
  change u = w at same
  subst u
  have selected := ((hoare_iff_run_ambient _ _ _).mp (DumpReservation.walk_cursor d ctx skb)
    w a walk w ac True.intro walking).trans cursor
  exact finish _ _ old _ _ _ _ _ _ selected account ac b rest

theorem chunk (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) (old : Option Owner)
    (cursor : ctx.nextPeer = old.map Owner.slot)
    (account : Credits carriers (old.toList ++ loans) w) (a b : Ambient)
    (run : ((wgGetDeviceDump ctx seq skb).run w).run a = .ok ((result,v),b)) :
    ∃ next : Option Owner, result.ctx.nextPeer = next.map Owner.slot ∧
      Credits carriers (next.toList ++ loans) v := by
  rw [wgGetDeviceDump_source,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,read,ar,getter,rest⟩ := run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp getDev_sameWGStore w a d read ar getter
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨⟨s,flags,attrs⟩,header,ah,headerRun,tailRun⟩ := rest
  have headerSame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (deviceDumpHeader_sameWGStore d ctx seq skb) read ar (s,flags,attrs) header ah headerRun
  exact tail d ctx s flags attrs old cursor (account.store (headerSame.trans same)) ah b tailRun

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Dump
