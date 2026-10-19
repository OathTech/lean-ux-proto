import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollPhaseFrames

/-! Whole original poll composition retains the exact peer account and
subtracts only the selected packets in its actual removal history. Normal
endpoints restore the stable remainder; Stops have no invented world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders RxJoint PollCarrier

def Loop (initial : RxCredits.Ledger) (loans : Reservations) (acc : Nat × Gro × Bool)
    (h : List RxJoint.Event) (w : World) : Prop := Boundary initial loans h w ∧ acc.2.2 = false

def Exit (initial : RxCredits.Ledger) (loans : Reservations) (pid : PeerId) (acc : Nat × Gro × Bool)
    (h : List RxJoint.Event) (w : World) : Prop :=
  Boundary initial loans h w ∧ (acc.2.2 = true → ColdHead pid w.wg)

theorem cleanup_bind (initial : RxCredits.Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer = pid) (tail : Obs α)
    (next : PrefixEnsures (Boundary initial loans) (fun _ => True) tail Q) :
    PrefixEnsures (Bare initial loans pid skb stamp) (fun _ => True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _ ← liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))
          tail) Q := by
  simpa only [bind_assoc] using PrefixEnsures.bind
    (cleanup initial loans pid skb stamp pkt flag guard) (fun u => by cases u; exact next)

theorem cleanup_live_bind (initial : RxCredits.Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer = pid) (tail : Obs α)
    (next : PrefixEnsures (Boundary initial loans) (fun _ => True) tail Q) :
    PrefixEnsures (Live initial loans pid skb stamp pkt) (fun _ => True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _ ← liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))
          tail) Q :=
  (cleanup_bind initial loans pid skb stamp pkt flag guard tail next).consequence
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

macro "exact_poll_step" : tactic => `(tactic|
  repeat' first
    | rx_phase_reduce
    | (rx_phase_head plain Pure.pure
       first
         | exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
         | exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => ⟨hi,rfl⟩)
         | exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => ⟨hi,fun bad => by cases bad⟩))
    | (rx_phase_head plain invariant; apply stop_bind (invariant _) (fun _ => ⟨_,rfl⟩))
    | (rx_phase_head plain unsupported; apply stop_bind (unsupported _) (fun _ => ⟨_,rfl⟩))
    | (rx_phase_head plain RxJoint.drop; apply PrefixEnsures.bind (Poll.drop _ _ _ _ _ _ _))
    | (rx_phase_head plain RxJoint.consume; apply PrefixEnsures.bind (Poll.consume _ _ _ _ _ _ _ _ (by simp_all)))
    | (rx_phase_head plain ForIn.forIn; apply keep_bind _ _ (option_bare _ _ _ _ _ _ _))
    | (rx_phase_head plain keypairPutPrefix
       first
         | apply cleanup_live_bind _ _ _ _ _ _ _ (by simp_all)
         | apply cleanup_bind _ _ _ _ _ _ _ (by simp_all))
    | (rx_phase_head receipt counterValidatePrefix; apply keep_bind _ _ (Poll.live_counter _ _ _ _ _ _ _))
    | (rx_phase_head receipt branch
       apply keep_bind _ _ (Poll.live_receipt_lift _
         (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))
         _ (fun _ => rfl)))
    | (rx_phase_head receipt endpointFromSkb
       apply keep_bind _ _ (Poll.live_receipt_lift _
         (liftWG_sameProductStore _ (endpointFromSkb_sameWGStore _)) _ (fun _ => rfl)))
    | (rx_phase_head plain branch
       first
         | apply keep_bind _ _ (Poll.live_lift _ (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h)))
         | apply keep_bind _ _ (Poll.context_lift _ _ _ _ (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))))
    | (rx_phase_head plain ite; apply PrefixEnsures.ite)
    | rx_phase_intro
    | rx_phase_match
    | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem tail (initial : RxCredits.Ledger) (loans : Reservations) (pid budget : Nat)
    (acc : Nat × Gro × Bool) :
    PrefixEnsures (Exit initial loans pid acc) (fun _ => True)
      (do
        if !acc.2.2 && acc.1 < budget then liftPrefix (invariant "the rx_queue did not drain")
        if ← liftPrefix (branch .rxPollComplete (acc.1 < budget)) then
          access (liftWGObserver (completeAccess pid))
          flushAll acc.2.1
        else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
        return acc.1)
      (fun _ => Boundary initial loans) := by
  obtain ⟨n,g,drained⟩ := acc
  by_cases room : n < budget
  · cases drained with
    | false =>
      simp only [Bool.not_false,room,decide_true,Bool.true_and,ite_true]
      apply stop_bind (invariant _) (fun _ => ⟨_,rfl⟩)
    | true =>
      simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false]
      apply stable_branch_bind (fun h w =>
        (∃ holders, Phased holders (rest initial h) loans w ∧ StableRx (rest initial h) w) ∧
          (true = true → ColdHead pid w))
      simp only [room,decide_true,ite_true]
      apply PrefixEnsures.bind ((complete initial loans pid).consequence
        (fun _ _ hi => ⟨hi.1,hi.2 True.intro⟩) (fun _ _ _ hi => hi))
      intro u
      cases u
      apply keep_bind _ _ (flush [] initial loans g)
      intro u
      cases u
      exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
  · simp only [room,decide_false,Bool.and_false,Bool.false_eq_true,ite_false]
    apply stable_branch_bind (fun h w =>
      (∃ holders, Phased holders (rest initial h) loans w ∧ StableRx (rest initial h) w) ∧
        (drained = true → ColdHead pid w))
    simp only [Bool.false_eq_true,ite_false]
    apply stop_bind (unsupported _) (fun _ => ⟨_,rfl⟩)

theorem preserves (initial : RxCredits.Ledger) (loans : Reservations) (pid budget : Nat) :
    PrefixPreserves (Boundary initial loans) (fun _ => True) (RxJoint.poll pid budget) := by
  change PrefixEnsures (Boundary initial loans) (fun _ => True) _ (fun _ => Boundary initial loans)
  unfold RxJoint.poll
  apply stable_branch_bind (fun h w => ∃ holders,
    Phased holders (rest initial h) loans w ∧ StableRx (rest initial h) w)
  split
  · exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind (Q := Exit initial loans pid)
    · apply PrefixEnsures.consequence (P := Loop initial loans (0,({} : Gro),false))
        (Q := Exit initial loans pid) ?_ (fun _ _ hi => ⟨hi,rfl⟩) (fun _ _ _ hi => hi)
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      apply stable_forIn_exit _ _ _ (Loop initial loans) (Exit initial loans pid)
        (fun _ => True) (fun _ _ _ _ => True.intro) (fun _ _ _ _ => True.intro)
        (fun _ _ _ hi => ⟨hi.1,fun bad => by rw [hi.2] at bad; cases bad⟩)
      intro index acc
      obtain ⟨n,g,drained⟩ := acc
      apply stable_assuming (drained = false)
      intro stopped
      subst drained
      apply PrefixEnsures.bind (peek initial loans pid)
      intro first
      apply PrefixEnsures.bind (ready initial loans pid first)
      intro go
      cases go with
      | false =>
        simp only [Bool.not_false,ite_true]
        exact PrefixEnsures.pure (fun _ _ _ => True.intro)
          (fun _ _ hi => ⟨hi.1,fun _ => hi.2.2.1 rfl⟩)
      | true =>
        simp only [Bool.not_true,Bool.false_eq_true,ite_false]
        cases first with
        | none => apply stop_bind (invariant _) (fun _ => ⟨_,rfl⟩)
        | some id =>
          apply PrefixEnsures.bind (capture initial loans pid id)
          intro captured
          obtain ⟨pkt,stamp⟩ := captured
          exact_poll_step
    · intro acc
      exact tail initial loans pid budget acc

theorem normal (pid : PeerId) (budget : Nat) (w v : World) (n : Nat)
    (initial : RxCredits.Ledger) (loans : Reservations) (prior : List LifetimeEvent)
    (before : ExactBoundary initial loans w.wg)
    (run : (WG.rxPoll pid budget (fun packets => packets.forM Leanux.Env.deliverInner)).run w = .ok (n,v)) :
    let h := (runPrefix (RxJoint.poll pid budget) w (seed prior)).2
    ExactBoundary (remaining initial (removedPackets h)) loans v.wg ∧
      ∀ packet ∈ removedPackets h, packetAt v.wg packet = none := by
  have observed := (poll_erases pid budget w (seed prior)).trans run
  have post := (preserves initial loans pid budget w (seed prior) (Boundary.start before prior)).choose_spec.2.2
  rw [observed] at post
  have exactAccount := post.exact
  refine ⟨exactAccount,?_⟩
  obtain ⟨holders,account⟩ := exactAccount
  exact fun packet member => remaining_inventory_gone account.funded.carriers.inventory member

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
