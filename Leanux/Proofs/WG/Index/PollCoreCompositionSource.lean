import Leanux.Proofs.WG.Queues.PollPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.PollCore.PollSource
open Leanux Leanux.WG Queues Leanux.Proofs.Logged Lifetimes
open RxJoint

theorem poll_preserves_fixed_variant {E : Type}
    (P Q : List E→World→Prop) (S : List E→Prop)
    (old : {α : Type}→Obs α→PrefixM E α)
    (receive : Gro→Entry→PrefixM E Gro) (flushAll : Gro→PrefixM E Unit)
    (pid : PeerId) (budget : Nat)
    (safeP : ∀h w,P h w→S h) (safeQ : ∀h w,Q h w→S h)
    (enter : ∀h w,Q h w→P h w)
    (peek : PrefixPreserves P S (old (access (liftWGObserver (peekAccess pid)))))
    (ready : ∀first, PrefixPreserves P S (old (access (liftWGObserver (readyAccess first)))))
    (captured : ∀id, PrefixPreserves P S (old (capture id)))
    (dropped : ∀n id stamp, PrefixPreserves P S (old (drop pid n id stamp)))
    (state : ∀n id stamp (pkt : RxPacket), PrefixPreserves P S
      (old (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState n id stamp pkt))))
    (counter : ∀n id stamp (pkt : RxPacket), PrefixPreserves P S
      (old (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (Event.checkedCounter n id stamp pkt))))
    (endpoint : ∀n id stamp (pkt : RxPacket), PrefixPreserves P S
      (old (receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
        (Event.checkedEndpoint n id stamp pkt))))
    (consumed : ∀n id stamp pkt ep,PrefixPreserves P S (old (consume pid n id stamp pkt ep)))
    (keypair : ∀id,PrefixPreserves P S (old (access (liftWGObserver (keypairPutPrefix (some id) false)))))
    (peer : PrefixPreserves P S (old (access (liftWGObserver (peerPutMixed (some pid))))))
    (free : ∀id,PrefixPreserves P S (old (access (liftWGObserver (freeRxSkbPrefix id)))))
    (complete : PrefixEnsures P S (old (access (liftWGObserver (completeAccess pid)))) (fun _=>Q))
    (noBudget : ∀b,PrefixPreserves Q S (liftPrefix (branch .rxPollNoBudget b)))
    (counterInvalid : ∀b,PrefixPreserves P S (liftPrefix (branch .rxPollCounterInvalid b)))
    (endpointFailed : ∀b,PrefixPreserves P S (liftPrefix (branch .rxPollEndpointFailed b)))
    (freeDecision : ∀b,PrefixPreserves P S (liftPrefix (branch .rxPollFree b)))
    (budgetDone : ∀b,PrefixPreserves P S (liftPrefix (branch .rxPollBudgetDone b)))
    (completeDecision : ∀b,PrefixPreserves P S (liftPrefix (branch .rxPollComplete b)))
    (received : ∀g e,PrefixPreserves P S (receive g e))
    (flushed : ∀g,PrefixPreserves Q S (flushAll g)) :
    PrefixPreserves Q S (RxJoint.PollSource.pollWith old receive flushAll pid budget) := by
  unfold RxJoint.PollSource.pollWith
  apply PrefixEnsures.bind (Q:=fun _=>Q) (noBudget _)
  intro noBudget
  cases noBudget with
  | true =>
    simp only [ite_true]
    exact PrefixPreserves.pure safeQ 0
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    apply PrefixEnsures.bind (Q:=fun _=>P)
    · apply PrefixEnsures.consequence (P:=P) (Q:=fun _=>P) ?_ enter (fun _ _ _ hi=>hi)
      change PrefixPreserves P S _
      repeat' first
        | (poll_preserve_head old
           first
           | with_reducible exact peek
           | with_reducible exact ready _
           | with_reducible exact captured _
           | with_reducible exact dropped _ _ _
           | with_reducible exact state _ _ _ _
           | with_reducible exact counter _ _ _ _
           | with_reducible exact endpoint _ _ _ _
           | with_reducible exact consumed _ _ _ _ _
           | with_reducible exact keypair _
           | with_reducible exact peer
           | with_reducible exact free _)
        | (poll_preserve_head receive; exact received _ _)
        | (poll_preserve_head liftPrefix
           first
           | with_reducible exact counterInvalid _
           | with_reducible exact endpointFailed _
           | with_reducible exact freeDecision _
           | with_reducible exact budgetDone _
           | with_reducible exact RxJoint.PollSource.invariant_preserves safeP _)
        | (poll_preserve_head Pure.pure; exact PrefixPreserves.pure safeP _)
        | (poll_preserve_head Bind.bind; apply PrefixPreserves.bind)
        | (poll_preserve_head ForIn.forIn
           first | apply PrefixPreserves.range | apply PrefixPreserves.forIn)
        | (poll_preserve_head ite; apply PrefixPreserves.ite)
        | exact safeP
        | rx_phase_reduce
        | rx_phase_intro
        | rx_phase_match
    · intro acc
      rcases acc with ⟨n,g,drained⟩
      split
      · intro w h hi
        have stopped : (invariant "the rx_queue did not drain" : Leanux.M Unit).run w =
            .error (.invariant "the rx_queue did not drain") := rfl
        simp only [runPrefix_bind,runPrefix_lift,stopped]
        exact ⟨[],by simp,safeP h w hi,True.intro⟩
      · apply PrefixEnsures.bind (Q:=fun _=>P) (completeDecision _)
        intro doComplete
        cases doComplete with
        | false =>
          simp only [Bool.false_eq_true,ite_false]
          intro w h hi
          obtain ⟨stop,stopped⟩ : ∃stop,
              (unsupported "a NAPI poll that used its whole budget (a repoll)" : Leanux.M Unit).run w =
                .error stop := ⟨_,rfl⟩
          simp only [runPrefix_bind,runPrefix_lift,stopped]
          exact ⟨[],by simp,safeP h w hi,True.intro⟩
        | true =>
          simp only [ite_true]
          exact PrefixEnsures.bind complete (fun _=>
            PrefixEnsures.bind (flushed g) (fun _=>PrefixPreserves.pure safeQ n))

end Leanux.Proofs.WG.Index.PollCore.PollSource
