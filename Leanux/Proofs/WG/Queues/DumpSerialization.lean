import Leanux.Proofs.WG.Queues.DumpReservation
import Leanux.Proofs.WG.Packets.AddressShape

namespace Leanux.Proofs.WG.Queues.RxCredits.DumpReservation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.NetlinkDump

private theorem result_step (a : WG.M α) (f : α → WG.M β) (Q : β → Prop)
    (h : ∀ x, Hoare (f x) (fun _ => True) (fun r _ => Q r)) :
    Hoare (a >>= f) (fun _ => True) (fun r _ => Q r) := by
  refine hoare_bind a f ?_ h
  exact (hoare_iff_run_ambient _ _ _).mpr (fun _ _ _ _ _ _ _ => trivial)

private theorem result_pure (x : α) (Q : α → Prop) (h : Q x) :
    Hoare (pure x : WG.M α) (fun _ => True) (fun r _ => Q r) :=
  hoare_consequence (hoare_pure x _) (fun _ h => h) (fun _ _ hr => hr.1 ▸ h)

private theorem result_then (a : WG.M α) (f : α → WG.M β) (P : α → Prop) (Q : β → Prop)
    (ha : Hoare a (fun _ => True) (fun x _ => P x))
    (hf : ∀ x, P x → Hoare (f x) (fun _ => True) (fun r _ => Q r)) :
    Hoare (a >>= f) (fun _ => True) (fun r _ => Q r) := by
  refine hoare_bind a f ha ?_
  intro x
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a r v b hp run
  exact (hoare_iff_run_ambient _ _ _).mp (hf x hp) w a r v b trivial run

private theorem result_loop (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
    (P : β → Prop) (hi : P init)
    (hf : ∀ x b, P b → Hoare (f x b) (fun _ => True) (fun r _ => P r.value)) :
    Hoare (forIn xs init f) (fun _ => True) (fun r _ => P r) := by
  induction xs generalizing init with
  | nil =>
    rw [List.forIn_nil]
    exact result_pure init P hi
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply result_then _ _ (fun r => P r.value) P (hf x init hi)
    intro step hp
    cases step with
    | done b => exact result_pure b P hp
    | yield b => exact ih b hp

private theorem result_stop (msg : String) (Q : α → Prop) :
    Hoare (invariant msg : WG.M α) (fun _ => True) (fun r _ => Q r) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a r v b _ run
  change Except.error _ = Except.ok _ at run
  cases run

private theorem result_unsupported (msg : String) (Q : α → Prop) :
    Hoare (unsupported msg : WG.M α) (fun _ => True) (fun r _ => Q r) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a r v b _ run
  change Except.error _ = Except.ok _ at run
  cases run

private theorem result_ite (p : Prop) [Decidable p] (a b : WG.M α) (Q : α → Prop)
    (ha : p → Hoare a (fun _ => True) (fun r _ => Q r))
    (hb : ¬p → Hoare b (fun _ => True) (fun r _ => Q r)) :
    Hoare (if p then a else b) (fun _ => True) (fun r _ => Q r) := by
  by_cases hp : p
  · simpa only [hp, ↓reduceIte] using ha hp
  · simpa only [hp, ↓reduceIte] using hb hp

open Lean Meta Elab Tactic in
elab "cursor_result_match" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Hoare do throwError "expected Hoare"
  let args := target.getAppArgs
  unless args.size ≥ 3 do throwError "missing action"
  let action := args[args.size - 3]!.consumeMData.headBeta
  let some _ ← Lean.Meta.matchMatcherApp? action | throwError "not a top matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

macro "cursor_basic" : tactic => `(tactic|
  first
    | (packet_hoare_head Pure.pure
       apply result_pure
       rfl)
    | (packet_hoare_head Leanux.unsupported
       exact result_unsupported _ _)
    | (packet_hoare_head Leanux.invariant
       exact result_stop _ _)
    | (packet_bind_head Leanux.unsupported
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a r v b hi run
       cases run)
    | (packet_hoare_head Bind.bind
       fail_if_success (packet_bind_head ForIn.forIn)
       apply result_step
       intro x
       try dsimp only)
    | (packet_hoare_head ite
       apply result_ite
       all_goals intro h)
    | (packet_hoare_head dite
       split <;> try dsimp only)
    | cursor_result_match)

/-- Serialization preserves the source cursor even on its split/cancel returns. -/
theorem allowed_cursor (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Lean.Json)) (node : Option NodeId) :
    Hoare (getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs node) (fun _ => True)
      (fun r _ => r.2.1.nextPeer = ctx.nextPeer) := by
  unfold getPeerDumpAllowedSource
  dsimp only
  repeat' cursor_basic
  all_goals
    apply result_then _ _
      (fun s : Option (NlSkb × DumpCtx × PeerDump) × NlSkb × Array Lean.Json =>
        ∀ r, s.1=some r → r.2.1.nextPeer=ctx.nextPeer)
    · apply result_loop
      · intro r impossible; cases impossible
      · intro id acc _
        repeat' first
          | (packet_hoare_head Pure.pure; apply result_pure; simp)
          | cursor_basic
    · intro acc hp
      rcases acc with ⟨out,skb,ips⟩
      cases out with
      | none =>
        dsimp only
        repeat' cursor_basic
      | some r => exact result_pure r _ (hp r rfl)

/-- The complete peer serializer leaves the old cursor untouched. -/
theorem peer_tail_cursor (p : Peer) (ctx : DumpCtx) (skb : NlSkb) :
    Hoare (getPeerDumpTailSource p ctx skb) (fun _ => True)
      (fun r _ => r.2.1.nextPeer=ctx.nextPeer) := by
  unfold getPeerDumpTailSource
  dsimp only
  generalize skb.put (nlaTotal 0) = put0
  rcases put0 with ⟨fail0,skb0⟩
  dsimp only
  generalize skb0.put (nlaTotal 32) = put1
  rcases put1 with ⟨fail1,skb1⟩
  dsimp only
  generalize skb1.put (nlaTotal 32) = put2
  rcases put2 with ⟨fail2,skb2⟩
  dsimp only
  generalize skb2.put (nlaTotal 16) = put3
  rcases put3 with ⟨fail3,skb3⟩
  dsimp only
  generalize skb3.put (nlaTotal 2) = put4
  rcases put4 with ⟨fail4,skb4⟩
  dsimp only
  generalize skb4.put (nlaTotal 8) = put5
  rcases put5 with ⟨fail5,skb5⟩
  dsimp only
  generalize skb5.put (nlaTotal 8) = put6
  rcases put6 with ⟨fail6,skb6⟩
  dsimp only
  generalize skb6.put (nlaTotal 4) = put7
  rcases put7 with ⟨fail7,skb7⟩
  dsimp only
  generalize skb7.put (nlaTotal 16) = put8
  rcases put8 with ⟨fail8,skb8⟩
  dsimp only
  generalize skb7.put (nlaTotal 28) = put9
  rcases put9 with ⟨fail9,skb9⟩
  dsimp only
  repeat' first
    | (packet_hoare_head getPeerDumpAllowedSource; exact allowed_cursor _ _ _ _ _ _ _)
    | cursor_basic

theorem peer_cursor (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    Hoare (getPeerDump pid ctx skb) (fun _ => True)
      (fun r _ => r.2.1.nextPeer=ctx.nextPeer) := by
  rw [getPeerDump_source]
  exact result_step _ _ _ (fun p => peer_tail_cursor p ctx skb)

/-- The existing device walk retains its input cursor on every normal return. -/
theorem walk_cursor (d : Device) (ctx : DumpCtx) (skb : NlSkb) :
    Hoare (walkSource d ctx skb) (fun _ => True)
      (fun r _ => r.1.nextPeer=ctx.nextPeer) := by
  unfold walkSource
  dsimp only
  repeat' cursor_basic
  apply result_then _ _
    (fun acc : DumpCtx × Option PeerId × NlSkb × Bool × Array PeerDumpAttrs =>
      acc.1.nextPeer=ctx.nextPeer)
  · apply result_loop
    · rfl
    · intro pid acc hacc
      apply result_step
      intro _
      apply result_step
      intro _
      apply result_then _ _ (fun r => r.2.1.nextPeer=acc.1.nextPeer) _
        (peer_cursor pid acc.1 acc.2.2.1)
      intro out hout
      rcases out with ⟨s,c,r⟩
      cases r <;> dsimp only
      all_goals
        apply result_step
        intro _
        apply result_pure
        exact hout.trans hacc
  · intro acc hacc
    repeat' first
      | (packet_hoare_head Pure.pure; apply result_pure; exact hacc)
      | cursor_basic


/-- The original tail exchanges exactly its supplied old cursor reservation.
The walk alignment is proved from serialization, rather than assumed. -/
theorem tail_normal (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (device : List (String × Lean.Json)) (old : Option Owner)
    (cursor : ctx.nextPeer=old.map Owner.slot)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (run : ((deviceDumpTailSource d ctx skb flags device).run w).run a=.ok ((result,v),b)) :
    ∃ next : Option Owner, result.ctx.nextPeer=next.map Owner.slot ∧
      ClearWork.Inv cs (next.toList ++ loans) v := by
  apply tail_from_walk d ctx skb flags device old hi a b _ run
  intro out u ac walkRun
  exact ((hoare_iff_run_ambient _ _ _).mp (walk_cursor d ctx skb)
    w a out u ac trivial walkRun).trans cursor

/-- A full native dump chunk preserves RX funding and the stable boundary,
replacing only the source cursor loan. It does not require an active-socket or
hasWg premise; those belong to the enclosing socket accounting invariant. -/
theorem dump_normal (ctx : DumpCtx) (prevSeq : UInt32) (skb : NlSkb) (old : Option Owner)
    (cursor : ctx.nextPeer=old.map Owner.slot)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (run : ((wgGetDeviceDump ctx prevSeq skb).run w).run a=.ok ((result,v),b)) :
    ∃ next : Option Owner, result.ctx.nextPeer=next.map Owner.slot ∧
      ClearWork.Inv cs (next.toList ++ loans) v := by
  rw [wgGetDeviceDump_source] at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,read,ar,getter,rest⟩ := run
  have getFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    getDev_sameWGStore w a d read ar getter
  have readInv : ClearWork.Inv cs (old.toList ++ loans) read :=
    ⟨hi.1.kernel getFrame,hi.2.kernel getFrame⟩
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨⟨s,flags,attrs⟩,header,ah,headerRun,tailRun⟩ := rest
  have headerFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (deviceDumpHeader_sameWGStore d ctx prevSeq skb) read ar (s,flags,attrs) header ah headerRun
  exact tail_normal d ctx s flags attrs old cursor
    ⟨readInv.1.kernel headerFrame,readInv.2.kernel headerFrame⟩ ah b tailRun

/-- The same cut applies to the existing lifetime observer at every incoming
journal and normal native/Ambient endpoint, without changing its Stop behavior. -/
theorem dump_observed (ctx : DumpCtx) (prevSeq : UInt32) (skb : NlSkb) (old : Option Owner)
    (cursor : ctx.nextPeer=old.map Owner.slot)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (history : List LifetimeEvent)
    (run : (runStatePrefix (wgGetDeviceDumpPrefix ctx prevSeq skb) w a history).1 =
      .ok ((result,v),b)) :
    ∃ next : Option Owner, result.ctx.nextPeer=next.map Owner.slot ∧
      ClearWork.Inv cs (next.toList ++ loans) v := by
  exact dump_normal ctx prevSeq skb old cursor hi a b
    ((wgGetDeviceDumpPrefix_erases ctx prevSeq skb w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.DumpReservation
