import Leanux.Proofs.WG.Queues.RxClearQueue
import Leanux.Proofs.WG.Queues.WorkReservations
import Leanux.Proofs.WG.Lifetimes.DumpAccess

/-! Source-owned dump cursor references. The native cuts consume the supplied
old cursor loan and retain only a newly acquired cursor loan. Socket activation
is a separate source invariant; neither hasWg nor spare count creates funding. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DumpReservation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.NetlinkDump

/-- Optional cursor payment preserves all other loans, allowing final deletion. -/
theorem put_normal (old : Option Owner) (hi : ClearWork.Inv cs (old.toList ++ loans) w)
    (a b : Ambient)
    (run : ((peerPut (old.map Owner.slot)).run w).run a = .ok (((),v),b)) :
    ClearWork.Inv cs loans v := by
  cases old with
  | none =>
    simp only [Option.map_none,Option.toList_none,List.nil_append] at hi run
    unfold peerPut at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨flag,checked,ac,decision,rest⟩ := run
    have result := (hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (fun g => g=w) .peerPutNull true) w a flag checked ac rfl decision
    rcases result with ⟨rfl,rfl⟩
    simp only [ite_true] at rest
    change Except.ok (((),checked),ac) = Except.ok (((),v),b) at rest
    cases rest
    exact hi
  | some o =>
    exact reservation_payment_stable hi.1 hi.2 a b run

/-- The done callback pays nextPeer unconditionally after its hasWg record. -/
theorem done_normal (ctx : DumpCtx) (old : Option Owner)
    (cursor : ctx.nextPeer = old.map Owner.slot)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (run : ((wgGetDeviceDone ctx).run w).run a = .ok (((),v),b)) :
    ClearWork.Inv cs loans v := by
  unfold wgGetDeviceDone at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨flag,checked,ac,decision,payment⟩ := run
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .getDoneHasWg ctx.hasWg) (fun g => g=w))
    w a flag checked ac rfl decision
  subst checked
  exact put_normal old hi ac b (cursor ▸ payment)

/-- The existing lifetime observer has exactly the same normal payment cut,
for arbitrary incoming history and Ambient endpoints. -/
theorem done_observed (ctx : DumpCtx) (old : Option Owner)
    (cursor : ctx.nextPeer = old.map Owner.slot)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (history : List LifetimeEvent)
    (run : (runStatePrefix (wgGetDeviceDonePrefix ctx) w a history).1 = .ok (((),v),b)) :
    ClearWork.Inv cs loans v := by
  exact done_normal ctx old cursor hi a b ((wgGetDeviceDonePrefix_erases ctx w a history).symm.trans run)

/-- The actual source's post-walk acquisition and payment, before serialization. -/
def replaceSource (ctx : DumpCtx) (nextCursor : Option PeerId) (done : Bool) : WG.M Unit := do
  if ← WG.andM (branch .dumpOutRetZero ((0 : Int) == 0))
      (WG.andM (branch .dumpOutNotDone !done) (branch .dumpOutHasCursor nextCursor.isSome)) then
    let some pid := nextCursor | invariant "unreachable"
    peerGet pid
  peerPut ctx.nextPeer

private theorem guard_normal (done : Bool) (nextCursor : Option PeerId) (a b : Ambient)
    (run : ((WG.andM (branch .dumpOutRetZero ((0 : Int) == 0))
      (WG.andM (branch .dumpOutNotDone !done) (branch .dumpOutHasCursor nextCursor.isSome))).run w).run a =
        .ok ((flag,v),b)) : flag = (!done && nextCursor.isSome) ∧ v=w := by
  cases done <;> cases nextCursor
  all_goals
    change Except.ok ((_,w),_) = Except.ok ((flag,v),b) at run
    cases run
    exact ⟨rfl,rfl⟩

/-- The original guarded acquisition returns its actual stamped source owner.
The old cursor loan is paid after the acquisition, including aliasing cursors. -/
theorem replace_normal (ctx : DumpCtx) (old : Option Owner) (nextCursor : Option PeerId) (done : Bool)
    (cursor : ctx.nextPeer = old.map Owner.slot)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (run : ((replaceSource ctx nextCursor done).run w).run a = .ok (((),v),b)) :
    ∃ next : Option Owner,
      next.map Owner.slot = (if done then none else nextCursor) ∧
      (∀ o, next = some o → ∃ d p, w.dev=some d ∧ d.peers[o.slot]?=some p ∧
        o=⟨d.ifindex,o.slot,p.internalId⟩ ∧ 0<p.refcount) ∧
      ClearWork.Inv cs (next.toList ++ loans) v := by
  unfold replaceSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨flag,checked,ac,decision,rest⟩ := run
  obtain ⟨rfl,rfl⟩ := guard_normal done nextCursor a ac decision
  cases done with
  | true =>
    simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false] at rest
    refine ⟨none,rfl,?_,put_normal old hi ac b (cursor ▸ rest)⟩
    intro o impossible; cases impossible
  | false =>
    cases nextCursor with
    | none =>
      simp only [Bool.not_false,Option.isSome_none,Bool.and_false,Bool.false_eq_true,ite_false] at rest
      refine ⟨none,rfl,?_,put_normal old hi ac b (cursor ▸ rest)⟩
      intro o impossible; cases impossible
    | some pid =>
      simp only [Bool.not_false,Option.isSome_some,Bool.true_and,ite_true,MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨u,got,ag,acquire,payment⟩ := rest
      cases u
      obtain ⟨d,p,hd,hp,pos,acquired⟩ := ClearWork.acquire hi ac ag acquire
      let o : Owner := ⟨d.ifindex,pid,p.internalId⟩
      have reordered : ClearWork.Inv cs (old.toList ++ (o :: loans)) got :=
        ⟨WorkReservations.carrier_loans_perm acquired.1
          (by simpa [o] using (List.perm_middle.symm : (o :: old.toList ++ loans).Perm (old.toList ++ o :: loans))), acquired.2⟩
      have paid := put_normal old reordered ag b (cursor ▸ payment)
      refine ⟨some o,rfl,?_,paid⟩
      intro chosen eq
      cases eq
      exact ⟨d,p,hd,hp,rfl,pos⟩

/-- Literal read-only peer walk preceding the reference replacement. -/
def walkSource (d : Device) (ctx0 : DumpCtx) (skb0 : NlSkb) :
    WG.M (DumpCtx × Option PeerId × NlSkb × Bool × Option (Array PeerDumpAttrs)) := do
  let mut ctx := ctx0
  let mut nextCursor := ctx.nextPeer
  let mut skb := skb0
  let nestStart := skb
  let (fail, s) := skb.put (nlaTotal 0); skb := s
  if ← branch .dumpNoPeersNest fail then unsupported "the peers nest does not fit a fresh chunk (unreachable)"
  let mut done := true
  let mut peers : Option (Array PeerDumpAttrs) := some #[]
  let cursorDead : WG.M Bool := do
    let some pid := ctx.nextPeer | invariant "unreachable"
    return (← getPeer pid).isDead
  if ← Leanux.WG.orM (branch .dumpPeerListEmpty d.peerList.isEmpty)
      (Leanux.WG.andM (branch .dumpCursorSet ctx.nextPeer.isSome) (do branch .dumpCursorDead (← cursorDead))) then
    skb := nestStart   -- nla_nest_cancel(skb, peers_nest); goto out
    peers := none
  else
    -- list_prepare_entry / list_for_each_entry_continue: from the peer
    -- after the cursor (the last completed one), or the first
    let fromPeers : List PeerId := match ctx.nextPeer with
      | none => d.peerList
      | some pid => (d.peerList.dropWhile (· != pid)).drop 1
    let mut ps : Array PeerDumpAttrs := #[]
    for pid in fromPeers do
      _ ← branch .dumpPeerIter true
      -- the handshake worker updates tx_bytes
      requireNotPending pid "dumping the peer"
      let (s, c, r) ← getPeerDump pid ctx skb
      skb := s; ctx := c
      match r with
      | .complete peer =>
        _ ← branch .dumpGetPeerFail false
        ps := ps.push peer
        nextCursor := some pid
      | .split peer =>
        _ ← branch .dumpGetPeerFail true
        ps := ps.push peer
        done := false
        break
      | .cancelled =>
        _ ← branch .dumpGetPeerFail true
        done := false
        break
    if done then _ ← branch .dumpPeerIter false
    peers := some ps
  return (ctx,nextCursor,skb,done,peers)

/-- Literal remainder of the existing chunk source after its peer walk. -/
def finishSource (seq : UInt32) (ctx : DumpCtx) (nextCursor : Option PeerId) (skb0 : NlSkb)
    (flags : Nat) (device : List (String × Lean.Json)) (done : Bool)
    (peers : Option (Array PeerDumpAttrs)) : WG.M DumpCall := do
  replaceSource ctx nextCursor done
  if ← branch .dumpRetErr ((0 : Int) != 0) then unsupported "unreachable: the header and the nests fit"
  let message := NlMessage.data flags device (peers.map (·.toList))
  let skb := { skb0 with messages := skb0.messages ++ [message] }
  if ← branch .dumpDone done then
    return { ret := 0, skb, ctx := { ctx with nextPeer := none }, prevSeq := seq }
  return { ret := Int.ofNat (NLMSG_GOODSIZE - skb.room), skb, ctx := { ctx with nextPeer := nextCursor }, prevSeq := seq }

/-- Exact source equality includes every record, early return and Stop. -/
theorem tail_factor (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (device : List (String × Lean.Json)) :
    deviceDumpTailSource d ctx skb flags device = (do
      let (ctx,nextCursor,skb,done,peers) ← walkSource d ctx skb
      finishSource d.deviceUpdateGen ctx nextCursor skb flags device done peers) := by
  simp only [deviceDumpTailSource,walkSource,finishSource,replaceSource,bind_assoc,pure_bind,(pinned_const _private.Leanux.Proofs.WG.NetlinkDump.DeviceSource.«0».Leanux.Proofs.WG.NetlinkDump.source_if_bind), (pinned_const _private.Leanux.Proofs.WG.NetlinkDump.DeviceSource.«0».Leanux.Proofs.WG.NetlinkDump.source_unsupported_bind_wg)]
  repeat' first
    | rfl
    | (apply (pinned_const _private.Leanux.Proofs.WG.NetlinkDump.DeviceSource.«0».Leanux.Proofs.WG.NetlinkDump.source_bind_congr); intro x)
    | split
    | simp only [bind_assoc]
  all_goals simp_all

/-- The returned context names exactly the new funded cursor. The acquisition
witness is from this source cut, before the old cursor's possible final release. -/
theorem finish_normal (seq : UInt32) (ctx : DumpCtx) (old : Option Owner)
    (nextCursor : Option PeerId) (skb : NlSkb) (flags : Nat)
    (device : List (String × Lean.Json)) (done : Bool) (peers : Option (Array PeerDumpAttrs))
    (cursor : ctx.nextPeer=old.map Owner.slot)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (run : ((finishSource seq ctx nextCursor skb flags device done peers).run w).run a = .ok ((result,v),b)) :
    ∃ next : Option Owner,
      result.ctx.nextPeer=next.map Owner.slot ∧
      (∀ o, next=some o → ∃ d p, w.dev=some d ∧ d.peers[o.slot]?=some p ∧
        o=⟨d.ifindex,o.slot,p.internalId⟩ ∧ 0<p.refcount) ∧
      ClearWork.Inv cs (next.toList ++ loans) v := by
  unfold finishSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,paid,ap,exchange,rest⟩ := run
  cases u
  obtain ⟨next,slot,origin,funded⟩ := replace_normal ctx old nextCursor done cursor hi a ap exchange
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨flag,checked,ac,decision,rest⟩ := rest
  obtain ⟨flagEq,same⟩ := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g => g=paid) .dumpRetErr false)
    paid ap flag checked ac rfl decision
  subst flag
  subst checked
  simp only [Bool.false_eq_true,ite_false] at rest
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨flag,checked,ad,decision,rest⟩ := rest
  obtain ⟨flagEq,same⟩ := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g => g=paid) .dumpDone done)
    paid ac flag checked ad rfl decision
  subst flag
  subst checked
  cases done <;> simp only [Bool.false_eq_true,ite_false,ite_true] at rest
  all_goals
    change Except.ok ((_,paid),ad) = Except.ok ((result,v),b) at rest
    cases rest
    exact ⟨next,slot.symm,origin,funded⟩

/-- Every normal original tail reaches the same read-only walk result and
literal cursor exchange/serialization suffix. This supplies its actual cut. -/
theorem tail_cut (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (device : List (String × Lean.Json)) (a b : Ambient)
    (run : ((deviceDumpTailSource d ctx skb flags device).run w).run a = .ok ((result,v),b)) :
    ∃ walk midway ambient,
      ((walkSource d ctx skb).run w).run a=.ok ((walk,midway),ambient) ∧
      ((finishSource d.deviceUpdateGen walk.1 walk.2.1 walk.2.2.1 flags device
        walk.2.2.2.1 walk.2.2.2.2).run midway).run ambient=.ok ((result,v),b) := by
  rw [tail_factor,MaterialOrigin.bind_ok_ambient] at run
  exact run

/-- The walk changes only Ambient records; its actual WG state is unchanged. -/
theorem walk_frame (d : Device) (ctx : DumpCtx) (skb : NlSkb) :
    SameView (id : WGWorld → WGWorld) (walkSource d ctx skb) := by
  have getter (pid : PeerId) : SameView (id : WGWorld → WGWorld) (getPeer pid) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact (getPeer_normal pid w v p a b run).1
  unfold walkSource
  repeat' first
    | (dump_kernel_head getPeer; exact getter _)
    | (dump_kernel_head getPeerDump; exact getPeerDump_sameWGWorld _ _ _)
    | (dump_kernel_head requireNotPending; exact SameView.pure _ _)
    | (dump_kernel_head branch; intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun g => g=initial))
    | (dump_kernel_head invariant; intro initial; exact hoare_liftAmbient (AmbientM.invariant _) (fun g => g=initial))
    | (dump_kernel_head unsupported; intro initial; exact hoare_liftAmbient (AmbientM.unsupported _) (fun g => g=initial))
    | (dump_kernel_head WG.orM; unfold WG.orM)
    | (dump_kernel_head WG.andM; unfold WG.andM)
    | dump_kernel_step

/-- This post-walk contract uses the actual original tail run. The supplied
cursor alignment is at its extracted read-only walk cut, not an assumed final state. -/
theorem tail_from_walk (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (device : List (String × Lean.Json)) (old : Option Owner)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (cursor : ∀ walk u ac, ((walkSource d ctx skb).run w).run a=.ok ((walk,u),ac) →
      walk.1.nextPeer=old.map Owner.slot)
    (run : ((deviceDumpTailSource d ctx skb flags device).run w).run a=.ok ((result,v),b)) :
    ∃ next : Option Owner, result.ctx.nextPeer=next.map Owner.slot ∧
      ClearWork.Inv cs (next.toList ++ loans) v := by
  obtain ⟨walk,u,ac,walkRun,finishRun⟩ := tail_cut d ctx skb flags device a b run
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (walk_frame d ctx skb) w a walk u ac walkRun
  change u=w at frame
  subst u
  obtain ⟨next,slot,_,funded⟩ := finish_normal _ _ old _ _ _ _ _ _ (cursor walk w ac walkRun) hi ac b finishRun
  exact ⟨next,slot,funded⟩

end Leanux.Proofs.WG.Queues.RxCredits.DumpReservation
