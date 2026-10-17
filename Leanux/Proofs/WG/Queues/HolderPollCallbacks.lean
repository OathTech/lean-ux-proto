import Leanux.Proofs.WG.Queues.HolderFrames
import Leanux.Proofs.WG.Queues.RxStableIteration

/-! Phase-aware callback cuts for the original poll observer. New TX/send
holders are retained while the actual removal journal and selected RX charge
keep their original meanings. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
open RxJoint PollCarrier

theorem gro_receive_normal {holders : DurableHolders} {w v : World}
    (g : GroState) (bytes : List UInt8) (hi : holders.Funded cs loans w.wg)
    (hs : StableRx stable w.wg)
    (run : (napiGroReceive (fun xs => xs.forM Leanux.Env.deliverInner) g bytes).run w = .ok (result,v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧
      (holders.absorb delta).Funded cs loans v.wg ∧ StableRx stable v.wg := by
  have post := (hoare_iff_run _ _ _).mp (groReceive_stack w.wg g bytes)
    w result v ⟨Transfer.refl w.wg,hi.carriers.keys⟩ run
  have passive := (hoare_iff_run _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groReceive_preserves)
      _ _ (fun xs => PassiveHolders.stack_preserves xs (passiveView w.wg)) g bytes) w result v rfl run
  have boundary := (hoare_iff_run _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxStableObserved.«0».Leanux.Proofs.WG.Queues.RxCredits.gro_stable)
      stable g bytes) w result v ⟨hi.carriers.keys,hs⟩ run
  obtain ⟨delta,handoff,funded⟩ := hi.transfer post.1 post.2 passive
  exact ⟨delta,handoff,funded,boundary.2⟩

theorem gro_flush_normal {holders : DurableHolders} {w v : World}
    (g : GroState) (hi : holders.Funded cs loans w.wg) (hs : StableRx stable w.wg)
    (run : (napiGroFlushAll (fun xs => xs.forM Leanux.Env.deliverInner) g).run w = .ok ((),v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧
      (holders.absorb delta).Funded cs loans v.wg ∧ StableRx stable v.wg := by
  have post := (hoare_iff_run _ _ _).mp (groFlush_stack w.wg g)
    w () v ⟨Transfer.refl w.wg,hi.carriers.keys⟩ run
  have passive := (hoare_iff_run _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groFlush_preserves)
      _ _ (fun xs => PassiveHolders.stack_preserves xs (passiveView w.wg)) g) w () v rfl run
  have boundary := (hoare_iff_run _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxStableObserved.«0».Leanux.Proofs.WG.Queues.RxCredits.flush_stable)
      stable g) w () v ⟨hi.carriers.keys,hs⟩ run
  obtain ⟨delta,handoff,funded⟩ := hi.transfer post.1 post.2 passive
  exact ⟨delta,handoff,funded,boundary.2⟩

theorem consume_accounted (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) (guard : pkt.peer = pid) :
    PrefixEnsures
      (Accounted (fun ls h w => Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w) loans)
      (fun _ => True) (consume pid n skb stamp pkt ep)
      (fun _ => Accounted (fun ls h w => Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans) := by
  apply normal_spec (consume_appends _ _ _ _ _ _)
  intro w h result v hi hr
  obtain ⟨holders,aligned,live,stable⟩ := hi
  have frame := removed_frame (consume_removed pid n skb stamp pkt ep) w h
  rcases live.1 with ⟨o,ho,hs,st⟩
  have hpacket : packetAt w.wg (packetOfStamp stamp) = some pkt := by
    rcases live.2 with ⟨he,hp⟩
    unfold packetAt packetOfStamp Lifetimes.packetStamp at *
    cases hd : w.wg.dev with
    | none => simp [RxDisposition.rxStore,RxDisposition.nativeRxStore,hd] at hp
    | some d => simpa [RxDisposition.rxStore,RxDisposition.nativeRxStore,hd,←he] using hp
  rw [consume_run] at hr
  cases ha : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk out t => cases out with
    | error e => simp [ha] at hr
    | ok out =>
      rcases out with ⟨out,a⟩
      have original := (access_erases (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h).symm.trans (congrArg Prod.fst ha)
      have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
        _ w a out original
      obtain ⟨delta,_,funded,boundary⟩ := consume_normal (holders := holders) (c := Selected stamp o)
        ⟨aligned,st⟩ stable hpacket guard w.ambient a.ambient native
      cases out <;> simp only [ha,Except.ok.injEq,Prod.mk.injEq] at hr
      all_goals obtain ⟨_,av⟩ := hr; subst a
      all_goals refine ⟨holders.absorb delta,funded.aligned,⟨o,ho,hs,?_⟩,?_⟩
      all_goals first
        | (change CarrierState (_ ++ remaining initial _) _ v.wg; rw [frame]; exact funded.carriers)
        | (change StableRx (remaining initial _) v.wg; rw [frame]; exact boundary)

theorem receive_context_accounted (front initial : Ledger) (loans : Reservations)
    (g : Gro) (entry : Entry) :
    PrefixPreserves (Accounted (fun ls h w => Context front initial ls h w ∧ StableAt initial h w) loans)
      (fun _ => True) (receive g entry) := by
  apply normal_spec (receive_appends g entry)
  intro w h result v hi run
  obtain ⟨holders,aligned,carriers,stable⟩ := hi
  have erase := projected_erases (receive_gro g entry) (napiGroReceiveTagged_erases g.forget entry.tag)
  have original : (napiGroReceive (fun xs => xs.forM Leanux.Env.deliverInner) g.erase entry.tag.bytes).run w =
      .ok (result.erase,v) := by
    have receipt := erase w h
    rw [run] at receipt
    exact receipt.symm
  obtain ⟨delta,_,funded,boundary⟩ := gro_receive_normal g.erase entry.tag.bytes
    ⟨aligned,carriers⟩ stable original
  have frame := removed_frame (receive_removed g entry) w h
  refine ⟨holders.absorb delta,funded.aligned,?_,?_⟩
  · change CarrierState (front ++ remaining initial _) _ v.wg
    rw [frame]
    exact funded.carriers
  · change StableRx (remaining initial _) v.wg
    rw [frame]
    exact boundary

theorem flush_context_accounted (front initial : Ledger) (loans : Reservations) (g : Gro) :
    PrefixPreserves (Accounted (fun ls h w => Context front initial ls h w ∧ StableAt initial h w) loans)
      (fun _ => True) (flushAll g) := by
  apply normal_spec (flushAll_appends g)
  intro w h result v hi run
  cases result
  obtain ⟨holders,aligned,carriers,stable⟩ := hi
  have erase := projected_erases (flushAll_gro g) (napiGroFlushAllTagged_erases g.forget).to_projected
  have original : (napiGroFlushAll (fun xs => xs.forM Leanux.Env.deliverInner) g.erase).run w =
      .ok ((),v) := by
    have receipt := erase w h
    rw [run] at receipt
    exact receipt.symm
  obtain ⟨delta,_,funded,boundary⟩ := gro_flush_normal g.erase ⟨aligned,carriers⟩ stable original
  have frame := removed_frame (flushAll_removed g) w h
  refine ⟨holders.absorb delta,funded.aligned,?_,?_⟩
  · change CarrierState (front ++ remaining initial _) _ v.wg
    rw [frame]
    exact funded.carriers
  · change StableRx (remaining initial _) v.wg
    rw [frame]
    exact boundary

theorem receive_bare_accounted (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (g : Gro) (entry : Entry) :
    PrefixPreserves
      (Accounted (fun ls h w => Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans)
      (fun _ => True) (receive g entry) := by
  apply normal_spec (receive_appends g entry)
  intro w h result v hi run
  obtain ⟨holders,aligned,⟨o,slot,stampEq,carriers⟩,stable⟩ := hi
  have post := (receive_context_accounted [Selected stamp o] initial loans g entry w h
    ⟨holders,aligned,carriers,stable⟩).choose_spec.2.2
  rw [run] at post
  obtain ⟨next,alignedNext,carriersNext,stableNext⟩ := post
  exact ⟨next,alignedNext,⟨o,slot,stampEq,carriersNext⟩,stableNext⟩

theorem option_bare_accounted (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (g : Gro) (out : Option Entry) :
    PrefixPreserves
      (Accounted (fun ls h w => Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans)
      (fun _ => True)
      (forIn out.toList g (fun e cur => do let next ← receive cur e; pure (.yield next))) := by
  cases out with
  | none => exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
  | some entry =>
    simpa only [Option.toList_some,List.forIn_cons,List.forIn_nil,bind_assoc,pure_bind,bind_pure] using
      receive_bare_accounted initial loans pid skb stamp g entry

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
