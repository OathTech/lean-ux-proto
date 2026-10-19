import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollContext

/-! The original poll's stack/GRO and consume callbacks preserve exact
selected-front accounting and the actual remaining-ledger history cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders RxJoint PollCarrier

theorem receive (front initial : RxCredits.Ledger) (loans : Reservations) (g : Gro) (entry : Entry) :
    PrefixPreserves (Context front initial loans) (fun _ => True) (RxJoint.receive g entry) := by
  apply PollCarrier.normal_spec (receive_appends g entry)
  intro w h result v before run
  obtain ⟨holders,account,stable⟩ := before
  have erase := projected_erases (receive_gro g entry) (napiGroReceiveTagged_erases g.forget entry.tag)
  have actual : (napiGroReceive (fun xs => xs.forM Leanux.Env.deliverInner) g.erase entry.tag.bytes).run w =
      .ok (result.erase,v) := by
    have receipt := erase w h
    rw [run] at receipt
    exact receipt.symm
  obtain ⟨delta,_,after,ready⟩ := account.gro_receive stable g.erase entry.tag.bytes actual
  have history := removed_frame (receive_removed g entry) w h
  refine ⟨holders.absorb delta,?_,?_⟩
  · change Phased _ (front ++ remaining initial _) loans v.wg
    rw [history]
    exact after
  · change StableRx (remaining initial _) v.wg
    rw [history]
    exact ready

theorem flush (front initial : RxCredits.Ledger) (loans : Reservations) (g : Gro) :
    PrefixPreserves (Context front initial loans) (fun _ => True) (flushAll g) := by
  apply PollCarrier.normal_spec (flushAll_appends g)
  intro w h result v before run
  cases result
  obtain ⟨holders,account,stable⟩ := before
  have erase := projected_erases (flushAll_gro g) (napiGroFlushAllTagged_erases g.forget).to_projected
  have actual : (napiGroFlushAll (fun xs => xs.forM Leanux.Env.deliverInner) g.erase).run w = .ok ((),v) := by
    have receipt := erase w h
    rw [run] at receipt
    exact receipt.symm
  obtain ⟨delta,_,after,ready⟩ := account.gro_flush stable g.erase actual
  have history := removed_frame (flushAll_removed g) w h
  refine ⟨holders.absorb delta,?_,?_⟩
  · change Phased _ (front ++ remaining initial _) loans v.wg
    rw [history]
    exact after
  · change StableRx (remaining initial _) v.wg
    rw [history]
    exact ready

theorem consume (initial : RxCredits.Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) (guard : pkt.peer = pid) :
    PrefixEnsures (Live initial loans pid skb stamp pkt) (fun _ => True)
      (RxJoint.consume pid n skb stamp pkt ep) (fun _ => Bare initial loans pid skb stamp) := by
  apply PollCarrier.normal_spec (consume_appends _ _ _ _ _ _)
  intro w h result v before run
  obtain ⟨⟨owner,ownerSlot,stampSlot,holders,account,stable⟩,selection⟩ := before
  have stored : packetAt w.wg (packetOfStamp stamp) = some pkt := by
    obtain ⟨epoch,cell⟩ := selection
    unfold packetAt packetOfStamp Lifetimes.packetStamp at *
    cases device : w.wg.dev with
    | none => simp [RxDisposition.rxStore,RxDisposition.nativeRxStore,device] at cell
    | some d => simpa [RxDisposition.rxStore,RxDisposition.nativeRxStore,device,←epoch] using cell
  have history := removed_frame (consume_removed pid n skb stamp pkt ep) w h
  rw [consume_run] at run
  cases accessRun : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk outcome journal =>
    cases outcome with
    | error e => simp [accessRun] at run
    | ok out =>
      obtain ⟨value,after⟩ := out
      have original := (access_erases (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h).symm.trans
        (congrArg Prod.fst accessRun)
      have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
        _ w after value original
      obtain ⟨delta,_,kept,ready⟩ := account.consume (c := Selected stamp owner) stable stored guard
        w.ambient after.ambient native
      cases value <;> simp only [accessRun,Except.ok.injEq,Prod.mk.injEq] at run
      all_goals obtain ⟨_,eq⟩ := run; subst after
      all_goals refine ⟨owner,ownerSlot,stampSlot,holders.absorb delta,?_,?_⟩
      all_goals first
        | (change Phased _ (_ ++ remaining initial _) loans v.wg; rw [history]; exact kept)
        | (change StableRx (remaining initial _) v.wg; rw [history]; exact ready)

theorem receive_bare (initial : RxCredits.Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (g : Gro) (entry : Entry) :
    PrefixPreserves (Bare initial loans pid skb stamp) (fun _ => True) (RxJoint.receive g entry) := by
  apply PollCarrier.normal_spec (receive_appends g entry)
  intro w h result v before run
  obtain ⟨owner,slot,stampSlot,account⟩ := before
  have post := (receive [Selected stamp owner] initial loans g entry w h account).choose_spec.2.2
  rw [run] at post
  exact ⟨owner,slot,stampSlot,post⟩

theorem option_bare (initial : RxCredits.Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (g : Gro) (out : Option Entry) :
    PrefixPreserves (Bare initial loans pid skb stamp) (fun _ => True)
      (forIn out.toList g (fun e cur => do let next ← RxJoint.receive cur e; pure (.yield next))) := by
  cases out with
  | none => exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
  | some entry =>
    simpa only [Option.toList_some,List.forIn_cons,List.forIn_nil,bind_assoc,pure_bind,bind_pure] using
      receive_bare initial loans pid skb stamp g entry

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
