import Leanux.Proofs.WG.Queues.RxStableIteration

/-! The actual finite receive poll restores the stable receive boundary on
normal return, using its stopped-head proof before NAPI completion. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
open RxJoint PollCarrier

def StableBoundary (initial : Ledger) (loans : Reservations) (h : List RxJoint.Event) (w : World) :=
  Ready initial loans h w ∧ StableAt initial h w

def StableLoop (initial : Ledger) (loans : Reservations) (acc : Nat × Gro × Bool)
    (h : List RxJoint.Event) (w : World) :=
  StableBoundary initial loans h w ∧ acc.2.2 = false

def StableExit (initial : Ledger) (loans : Reservations) (pid : PeerId) (acc : Nat × Gro × Bool)
    (h : List RxJoint.Event) (w : World) :=
  StableBoundary initial loans h w ∧ (acc.2.2 = true → ColdHead pid w.wg)

macro "stable_poll_step" : tactic => `(tactic|
  repeat' first
    | rx_phase_reduce
    | (rx_phase_head plain Pure.pure
       first
         | exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
         | exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => ⟨hi,rfl⟩)
         | exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => ⟨hi,fun bad => by cases bad⟩))
    | (rx_phase_head plain invariant; apply stop_bind (invariant _) (fun _ => ⟨_,rfl⟩))
    | (rx_phase_head plain unsupported; apply stop_bind (unsupported _) (fun _ => ⟨_,rfl⟩))
    | (rx_phase_head plain drop; apply PrefixEnsures.bind (stable_drop_observed _ _ _ _ _ _ _ (by assumption)))
    | (rx_phase_head plain consume; apply PrefixEnsures.bind (stable_consume_observed _ _ _ _ _ _ _ _ (by simp_all)))
    | (rx_phase_head plain ForIn.forIn; apply keep_bind _ _ (stable_bare_option _ _ _ _ _ _ _))
    | (rx_phase_head plain keypairPutPrefix
       first
         | apply stable_cleanup_live_bind _ _ _ _ _ _ _ (by simp_all)
         | apply stable_cleanup_bind _ _ _ _ _ _ _ (by simp_all))
    | (rx_phase_head receipt counterValidatePrefix; apply keep_bind _ _ (stable_live_counter _ _ _ _ _ _ _))
    | (rx_phase_head receipt branch
       apply keep_bind _ _ (stable_receipt_lift_observed _
         (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))
         _ (fun _ => rfl) (live_state _ _ _ _)))
    | (rx_phase_head receipt endpointFromSkb
       apply keep_bind _ _ (stable_receipt_lift_observed _
         (liftWG_sameProductStore _ (endpointFromSkb_sameWGStore _)) _ (fun _ => rfl) (live_endpoint _ _ _ _)))
    | (rx_phase_head plain branch
       first
         | apply keep_bind _ _ (stable_lift_observed _
             (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))
             (live_lift _ (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))))
         | apply keep_bind _ _ (stable_lift_observed _
             (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h))
             (context_lift _ _ _ _ (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) (fun w => productStoreView w = initial) (fun _ _ h => h)))))
    | (rx_phase_head plain ite; apply PrefixEnsures.ite)
    | rx_phase_intro
    | rx_phase_match
    | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem stable_poll_tail (initial : Ledger) (loans : Reservations) (pid budget : Nat)
    (acc : Nat × Gro × Bool) :
    PrefixEnsures (StableExit initial loans pid acc) (fun _ => True)
      (do
        if !acc.2.2 && acc.1 < budget then liftPrefix (invariant "the rx_queue did not drain")
        if ← liftPrefix (branch .rxPollComplete (acc.1 < budget)) then
          access (liftWGObserver (completeAccess pid))
          flushAll acc.2.1
        else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
        return acc.1)
      (fun _ => StableBoundary initial loans) := by
  rcases acc with ⟨n,g,drained⟩
  by_cases room : n < budget
  · cases drained with
    | false =>
      simp only [Bool.not_false,room,decide_true,Bool.true_and,ite_true]
      apply stop_bind (invariant _) (fun _ => ⟨_,rfl⟩)
    | true =>
      simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false]
      apply stable_branch_bind (fun h w =>
        (CarrierState (rest initial h) loans w ∧ StableRx (rest initial h) w) ∧ (true = true → ColdHead pid w))
      simp only [room,decide_true,ite_true]
      apply PrefixEnsures.bind ((stable_complete_observed initial loans pid).consequence
        (fun _ _ hi => ⟨hi.1.1,hi.1.2,hi.2 True.intro⟩) (fun _ _ _ hi => hi))
      intro u
      cases u
      apply keep_bind _ _ (stable_flush_observed initial loans g)
      intro u
      cases u
      exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
  · simp only [room,decide_false,Bool.and_false,Bool.false_eq_true,ite_false]
    apply stable_branch_bind (fun h w =>
      (CarrierState (rest initial h) loans w ∧ StableRx (rest initial h) w) ∧ (drained = true → ColdHead pid w))
    simp only [Bool.false_eq_true,ite_false]
    apply stop_bind (unsupported _) (fun _ => ⟨_,rfl⟩)

/-- The original observer, including all stopped prefixes, carries the same
remaining ledger and establishes StableRx at every normal poll endpoint. -/
theorem stable_poll_state (initial : Ledger) (loans : Reservations) (pid budget : Nat) :
    PrefixPreserves (StableBoundary initial loans) (fun _ => True) (poll pid budget) := by
  change PrefixEnsures (StableBoundary initial loans) (fun _ => True) _ (fun _ => StableBoundary initial loans)
  unfold poll
  apply stable_branch_bind (fun h w => CarrierState (rest initial h) loans w ∧ StableRx (rest initial h) w)
  split
  · exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind (Q := StableExit initial loans pid)
    · apply PrefixEnsures.consequence (P := StableLoop initial loans (0,({}:Gro),false))
        (Q := StableExit initial loans pid) ?_ (fun _ _ hi => ⟨hi,rfl⟩) (fun _ _ _ hi => hi)
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      apply stable_forIn_exit _ _ _ (StableLoop initial loans) (StableExit initial loans pid)
        (fun _ => True) (fun _ _ _ _ => True.intro) (fun _ _ _ _ => True.intro)
        (fun _ _ _ hi => ⟨hi.1,fun bad => by rw [hi.2] at bad; cases bad⟩)
      intro index acc
      rcases acc with ⟨n,g,drained⟩
      apply stable_assuming (drained = false)
      intro stopped
      subst drained
      apply PrefixEnsures.bind (stable_peek_observed initial loans pid)
      intro first
      apply PrefixEnsures.bind (stable_ready_observed initial loans pid first)
      intro go
      cases go with
      | false =>
        simp only [Bool.not_false,ite_true]
        exact PrefixEnsures.pure (fun _ _ _ => True.intro)
          (fun _ _ hi => ⟨⟨hi.1.1,hi.2.1⟩,fun _ => hi.2.2.1 True.intro⟩)
      | true =>
        simp only [Bool.not_true,Bool.false_eq_true,ite_false]
        cases first with
        | none => apply stop_bind (invariant _) (fun _ => ⟨_,rfl⟩)
        | some id =>
          apply PrefixEnsures.bind ((stable_capture_observed initial loans pid id).consequence
            (fun _ _ hi => ⟨hi.1,hi.2.1,hi.2.2.2 True.intro⟩) (fun _ _ _ hi => hi))
          intro captured
          rcases captured with ⟨pkt,stamp⟩
          apply PrefixEnsures.consequence (P := fun h w =>
            (Captured initial loans pid id (pkt,stamp) h w ∧ StableAt initial h w) ∧ pkt.state ≠ .uncrypted)
            (Q := _) ?_ (fun _ _ hi => ⟨⟨hi.1,hi.2.1⟩,hi.2.2⟩) (fun _ _ _ hi => hi)
          apply stable_assuming (pkt.state ≠ .uncrypted)
          intro ready
          stable_poll_step
    · intro acc
      exact stable_poll_tail initial loans pid budget acc

/-- The native poll uses the actual product Stack callback. Only the packet
identities selected by this execution's fresh removal suffix are subtracted;
no refcount, residency, credit, or successful-callback premise is added. -/
theorem poll_normal_stable (pid : PeerId) (budget : Nat) (w v : World) (n : Nat)
    (initial : Ledger) (loans : Reservations) (prior : List LifetimeEvent)
    (hi : CarrierState initial loans w.wg) (hs : StableRx initial w.wg)
    (hr : (WG.rxPoll pid budget (fun packets => packets.forM Leanux.Env.deliverInner)).run w = .ok (n,v)) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2
    CarrierState (remaining initial (removedPackets h)) loans v.wg ∧
      StableRx (remaining initial (removedPackets h)) v.wg ∧
      ∀ p ∈ removedPackets h, packetAt v.wg p = none := by
  have joint : (runPrefix (poll pid budget) w (seed prior)).1 = .ok (n,v) :=
    (poll_erases pid budget w (seed prior)).trans hr
  have start : StableBoundary initial loans (seed prior) w := by
    have empty : remaining initial [] = initial := List.filter_eq_self.mpr (fun _ _ => rfl)
    unfold StableBoundary StableAt Ready PollCarrier.Context rest
    rw [seed_removedPackets]
    simpa only [List.nil_append,empty] using And.intro hi hs
  have post := (stable_poll_state initial loans pid budget w (seed prior) start).choose_spec.2.2
  have endpoint : StableBoundary initial loans (runPrefix (poll pid budget) w (seed prior)).2 v := by
    simpa only [joint] using post
  exact ⟨endpoint.1,endpoint.2,fun p hp => remaining_inventory_gone endpoint.1.inventory hp⟩

end Leanux.Proofs.WG.Queues.RxCredits
