import Leanux.Proofs.WG.Queues.HolderPollPhases

/-! The actual finite receive poll retains every newly acquired durable holder
while restoring the stable receive boundary at its normal endpoint. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
open RxJoint PollCarrier

def FundedBoundary (initial : Ledger) (loans : Reservations) (h : List RxJoint.Event) (w : World) :=
  Accounted (StableBoundary initial) loans h w

def FundedLoop (initial : Ledger) (loans : Reservations) (acc : Nat × Gro × Bool)
    (h : List RxJoint.Event) (w : World) :=
  FundedBoundary initial loans h w ∧ acc.2.2 = false

def FundedExit (initial : Ledger) (loans : Reservations) (pid : PeerId) (acc : Nat × Gro × Bool)
    (h : List RxJoint.Event) (w : World) :=
  FundedBoundary initial loans h w ∧ (acc.2.2 = true → ColdHead pid w.wg)

macro "holder_poll_step" : tactic => `(tactic|
  repeat' first
    | rx_phase_reduce
    | (rx_phase_head plain Pure.pure
       first
         | exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
         | exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => ⟨hi,rfl⟩)
         | exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => ⟨hi,fun bad => by cases bad⟩))
    | (rx_phase_head plain invariant; apply stop_bind (invariant _) (fun _ => ⟨_,rfl⟩))
    | (rx_phase_head plain unsupported; apply stop_bind (unsupported _) (fun _ => ⟨_,rfl⟩))
    | (rx_phase_head plain drop; apply PrefixEnsures.bind (drop_accounted _ _ _ _ _ _ _ (by assumption)))
    | (rx_phase_head plain consume; apply PrefixEnsures.bind (consume_accounted _ _ _ _ _ _ _ _ (by simp_all)))
    | (rx_phase_head plain ForIn.forIn; apply keep_bind _ _ (option_bare_accounted _ _ _ _ _ _ _))
    | (rx_phase_head plain keypairPutPrefix
       first
         | apply cleanup_live_accounted_bind _ _ _ _ _ _ _ (by simp_all)
         | apply cleanup_accounted_bind _ _ _ _ _ _ _ (by simp_all))
    | (rx_phase_head receipt counterValidatePrefix; apply keep_bind _ _ (counter_accounted _ _ _ _ _ _ _))
    | (rx_phase_head receipt branch
       apply keep_bind _ _ (receipt_lift_accounted _
         (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))
         _ (fun _ => rfl) (fun ls => live_state (loans := ls) _ _ _ _) _))
    | (rx_phase_head receipt endpointFromSkb
       apply keep_bind _ _ (receipt_lift_accounted _
         (liftWG_sameProductStore _ (endpointFromSkb_sameWGStore _)) _ (fun _ => rfl) (fun ls => live_endpoint (loans := ls) _ _ _ _) _))
    | (rx_phase_head plain branch
       first
         | apply keep_bind _ _ (lift_accounted _
             (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))
             (fun ls => live_lift (loans := ls) _ (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))) _)
         | apply keep_bind _ _ (lift_accounted _
             (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))
             (fun ls => context_lift _ _ ls _ (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))) _))
    | (rx_phase_head plain ite; apply PrefixEnsures.ite)
    | rx_phase_intro
    | rx_phase_match
    | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem funded_poll_tail (initial : Ledger) (loans : Reservations) (pid budget : Nat)
    (acc : Nat × Gro × Bool) :
    PrefixEnsures (FundedExit initial loans pid acc) (fun _ => True)
      (do
        if !acc.2.2 && acc.1 < budget then liftPrefix (invariant "the rx_queue did not drain")
        if ← liftPrefix (branch .rxPollComplete (acc.1 < budget)) then
          access (liftWGObserver (completeAccess pid))
          flushAll acc.2.1
        else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
        return acc.1)
      (fun _ => FundedBoundary initial loans) := by
  rcases acc with ⟨n,g,drained⟩
  by_cases room : n < budget
  · cases drained with
    | false =>
      simp only [Bool.not_false,room,decide_true,Bool.true_and,ite_true]
      apply stop_bind (invariant _) (fun _ => ⟨_,rfl⟩)
    | true =>
      simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false]
      apply stable_branch_bind (fun h w =>
        (∃ holders : DurableHolders, holders.Aligned w ∧ CarrierState (rest initial h) (holders.owners ++ loans) w ∧ StableRx (rest initial h) w) ∧ (true = true → ColdHead pid w))
      simp only [room,decide_true,ite_true]
      apply PrefixEnsures.bind ((complete_accounted initial loans pid).consequence
        (fun _ _ ⟨⟨holders,aligned,carriers,stable⟩,cold⟩ => ⟨holders,aligned,carriers,stable,cold True.intro⟩) (fun _ _ _ hi => hi))
      intro u
      cases u
      apply keep_bind _ _ (flush_context_accounted [] initial loans g)
      intro u
      cases u
      exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
  · simp only [room,decide_false,Bool.and_false,Bool.false_eq_true,ite_false]
    apply stable_branch_bind (fun h w =>
      (∃ holders : DurableHolders, holders.Aligned w ∧ CarrierState (rest initial h) (holders.owners ++ loans) w ∧ StableRx (rest initial h) w) ∧ (drained = true → ColdHead pid w))
    simp only [Bool.false_eq_true,ite_false]
    apply stop_bind (unsupported _) (fun _ => ⟨_,rfl⟩)

/-- The original observer, including all stopped prefixes, carries the same
remaining ledger and establishes StableRx at every normal poll endpoint. -/
theorem funded_poll_state (initial : Ledger) (loans : Reservations) (pid budget : Nat) :
    PrefixPreserves (FundedBoundary initial loans) (fun _ => True) (poll pid budget) := by
  change PrefixEnsures (FundedBoundary initial loans) (fun _ => True) _ (fun _ => FundedBoundary initial loans)
  unfold poll
  apply stable_branch_bind (fun h w => ∃ holders : DurableHolders, holders.Aligned w ∧ CarrierState (rest initial h) (holders.owners ++ loans) w ∧ StableRx (rest initial h) w)
  split
  · exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind (Q := FundedExit initial loans pid)
    · apply PrefixEnsures.consequence (P := FundedLoop initial loans (0,({}:Gro),false))
        (Q := FundedExit initial loans pid) ?_ (fun _ _ hi => ⟨hi,rfl⟩) (fun _ _ _ hi => hi)
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      apply stable_forIn_exit _ _ _ (FundedLoop initial loans) (FundedExit initial loans pid)
        (fun _ => True) (fun _ _ _ _ => True.intro) (fun _ _ _ _ => True.intro)
        (fun _ _ _ hi => ⟨hi.1,fun bad => by rw [hi.2] at bad; cases bad⟩)
      intro index acc
      rcases acc with ⟨n,g,drained⟩
      apply stable_assuming (drained = false)
      intro stopped
      subst drained
      apply PrefixEnsures.bind (peek_accounted initial loans pid)
      intro first
      apply PrefixEnsures.bind (ready_accounted initial loans pid first)
      intro go
      cases go with
      | false =>
        simp only [Bool.not_false,ite_true]
        exact PrefixEnsures.pure (fun _ _ _ => True.intro)
          (fun _ _ ⟨holders,aligned,peek,stable,cold,_⟩ => ⟨⟨holders,aligned,peek.1,stable⟩,fun _ => cold True.intro⟩)
      | true =>
        simp only [Bool.not_true,Bool.false_eq_true,ite_false]
        cases first with
        | none => apply stop_bind (invariant _) (fun _ => ⟨_,rfl⟩)
        | some id =>
          apply PrefixEnsures.bind ((capture_accounted initial loans pid id).consequence
            (fun _ _ ⟨holders,aligned,peek,stable,_,ready⟩ => ⟨holders,aligned,peek,stable,ready True.intro⟩) (fun _ _ _ hi => hi))
          intro captured
          rcases captured with ⟨pkt,stamp⟩
          apply PrefixEnsures.consequence (P := fun h w =>
            Accounted (fun ls h w => Captured initial ls pid id (pkt,stamp) h w ∧ StableAt initial h w) loans h w ∧ pkt.state ≠ .uncrypted)
            (Q := _) ?_ (fun _ _ ⟨holders,aligned,captured,stable,ready⟩ => ⟨⟨holders,aligned,captured,stable⟩,ready⟩) (fun _ _ _ hi => hi)
          apply stable_assuming (pkt.state ≠ .uncrypted)
          intro ready
          holder_poll_step
    · intro acc
      exact funded_poll_tail initial loans pid budget acc

/-- Every normal actual poll endpoint retains the complete funded holder
account and subtracts exactly the selected removal suffix from its RX ledger. -/
theorem poll_normal_funded (pid : PeerId) (budget : Nat) (w v : World) (n : Nat)
    (initial : Ledger) (loans : Reservations) (prior : List LifetimeEvent)
    (hi : Boundary initial loans w.wg)
    (hr : (WG.rxPoll pid budget (fun packets => packets.forM Leanux.Env.deliverInner)).run w = .ok (n,v)) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2
    Boundary (remaining initial (removedPackets h)) loans v.wg ∧
      ∀ p ∈ removedPackets h, packetAt v.wg p = none := by
  have joint : (runPrefix (poll pid budget) w (seed prior)).1 = .ok (n,v) :=
    (poll_erases pid budget w (seed prior)).trans hr
  have start : FundedBoundary initial loans (seed prior) w := by
    obtain ⟨holders,funded,stable⟩ := hi
    have empty : remaining initial [] = initial := List.filter_eq_self.mpr (fun _ _ => rfl)
    refine ⟨holders,funded.aligned,?_⟩
    unfold StableBoundary StableAt Ready PollCarrier.Context rest
    rw [seed_removedPackets]
    simpa only [List.nil_append,empty] using And.intro funded.carriers stable
  have post := (funded_poll_state initial loans pid budget w (seed prior) start).choose_spec.2.2
  have endpoint : FundedBoundary initial loans (runPrefix (poll pid budget) w (seed prior)).2 v := by
    simpa only [joint] using post
  obtain ⟨holders,aligned,carriers,stable⟩ := endpoint
  exact ⟨⟨holders,⟨aligned,carriers⟩,stable⟩,fun p hp => remaining_inventory_gone carriers.inventory hp⟩

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
