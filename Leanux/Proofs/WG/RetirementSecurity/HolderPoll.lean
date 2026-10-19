import Leanux.Proofs.WG.RetirementSecurity.HolderPollFrames

/-! The original receive-poll observer transports the exact key-reference
account across its actual finite loop. Selected references are explicit
locals between dequeue and cleanup; GRO may stage new physical TX holders. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits Std.Do
open RxJoint PollCarrier DurableHolders

def KeyBoundary (sessions : List SessionOrigin.Receipt) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (temporary : Credits.Ledger) (initial : Ledger) (loans : Reservations) :=
  WithKeys sessions locals active temporary (Accounted (StableBoundary initial) loans)

def KeyLoop (sessions : List SessionOrigin.Receipt) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (temporary : Credits.Ledger) (initial : Ledger) (loans : Reservations)
    (acc : Nat × Gro × Bool) (h : List RxJoint.Event) (w : World) :=
  KeyBoundary sessions locals active temporary initial loans h w ∧ acc.2.2=false

def KeyExit (sessions : List SessionOrigin.Receipt) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (temporary : Credits.Ledger) (initial : Ledger) (loans : Reservations)
    (pid : PeerId) (acc : Nat × Gro × Bool) (h : List RxJoint.Event) (w : World) :=
  KeyBoundary sessions locals active temporary initial loans h w ∧ (acc.2.2=true → ColdHead pid w.wg)

theorem branch_store (decision : Decision) (value : Bool) : SameProductStore (branch decision value) :=
  fun initial=>productAmbient_spec (AmbientM.branch decision value) (fun w=>productStoreView w=initial) (fun _ _ before=>before)

macro "key_poll_step" : tactic => `(tactic|
  repeat' first
    | rx_phase_reduce
    | (rx_phase_head plain Pure.pure
       first
         | exact PrefixEnsures.pure (fun _ _ _=>True.intro) (fun _ _ hi=>hi)
         | exact PrefixEnsures.pure (fun _ _ _=>True.intro) (fun _ _ hi=>⟨hi,rfl⟩)
         | exact PrefixEnsures.pure (fun _ _ _=>True.intro) (fun _ _ hi=>⟨hi,fun bad=>by cases bad⟩))
    | (rx_phase_head plain invariant; apply stop_bind (invariant _) (fun _=>⟨_,rfl⟩))
    | (rx_phase_head plain unsupported; apply stop_bind (unsupported _) (fun _=>⟨_,rfl⟩))
    | (rx_phase_head plain RxJoint.drop; apply PrefixEnsures.bind (drop_phase _ _ _ _ _ _ _ (by assumption)))
    | (rx_phase_head plain RxJoint.consume; apply PrefixEnsures.bind (consume_phase _ _ _ _ _ _ _ _ (by simp_all)))
    | (rx_phase_head plain ForIn.forIn; apply keep_bind _ _ (option_phase _ _ _ _ _ _ _ _))
    | (rx_phase_head plain keypairPutPrefix
       first
         | apply cleanup_live_phase_bind _ _ _ _ _ _ _ (by simp_all)
         | apply cleanup_phase_bind _ _ _ _ _ _ _ (by simp_all))
    | (rx_phase_head receipt counterValidatePrefix; apply keep_bind _ _ (counter_phase _ _ _ _ _ _ _))
    | (rx_phase_head receipt branch
       apply keep_bind _ _ (receipt_local _ (branch_store _ _) _
         (receipt_lift_accounted _ (branch_store _ _) _ (fun _=>rfl)
           (fun ls=>live_state (loans:=ls) _ _ _ _) _)))
    | (rx_phase_head receipt endpointFromSkb
       apply keep_bind _ _ (receipt_local _ (liftWG_sameProductStore _ (endpointFromSkb_sameWGStore _)) _
         (receipt_lift_accounted _ (liftWG_sameProductStore _ (endpointFromSkb_sameWGStore _)) _ (fun _=>rfl)
           (fun ls=>live_endpoint (loans:=ls) _ _ _ _) _)))
    | (rx_phase_head plain branch
       first
         | apply keep_bind _ _ (lift_local _ (branch_store _ _) (lift_accounted _ (branch_store _ _)
             (fun ls=>live_lift (loans:=ls) _ (branch_store _ _)) _))
         | apply keep_bind _ _ (lift_keys _ (branch_store _ _) (lift_accounted _ (branch_store _ _)
             (fun ls=>context_lift _ _ ls _ (branch_store _ _)) _)))
    | (rx_phase_head plain ite; apply PrefixEnsures.ite)
    | rx_phase_intro
    | rx_phase_match
    | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem poll_tail (initial : Ledger) (loans : Reservations) (pid budget : Nat)
    (acc : Nat × Gro × Bool) :
    PrefixEnsures (KeyExit sessions locals active temporary initial loans pid acc) (fun _=>True)
      (do
        if !acc.2.2 && acc.1<budget then liftPrefix (invariant "the rx_queue did not drain")
        if ←liftPrefix (branch .rxPollComplete (acc.1<budget)) then
          access (liftWGObserver (completeAccess pid))
          flushAll acc.2.1
        else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
        return acc.1)
      (fun _=>KeyBoundary sessions locals active temporary initial loans) := by
  rcases acc with ⟨n,g,drained⟩
  by_cases room:n<budget
  · cases drained with
    | false=>
      simp only [Bool.not_false,room,decide_true,Bool.true_and,ite_true]
      apply stop_bind (invariant _) (fun _=>⟨_,rfl⟩)
    | true=>
      simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false]
      apply stable_branch_bind (fun h w=>
        ((∃holders:DurableHolders,holders.Aligned w ∧ CarrierState (rest initial h) (holders.owners++loans) w ∧ StableRx (rest initial h) w) ∧
          HolderAccount temporary w ∧ Support sessions locals active w) ∧ (true=true → ColdHead pid w))
      simp only [room,decide_true,ite_true]
      apply PrefixEnsures.bind ((complete_phase initial loans pid).consequence
        (fun _ _ ⟨⟨⟨holders,aligned,carriers,stable⟩,keys,support⟩,cold⟩=>
          ⟨⟨holders,aligned,carriers,stable,cold True.intro⟩,keys,support⟩) (fun _ _ _ hi=>hi))
      intro u
      cases u
      apply keep_bind _ _ (flush_phase initial loans g)
      intro u
      cases u
      exact PrefixEnsures.pure (fun _ _ _=>True.intro) (fun _ _ hi=>hi)
  · simp only [room,decide_false,Bool.and_false,Bool.false_eq_true,ite_false]
    apply stable_branch_bind (fun h w=>
      ((∃holders:DurableHolders,holders.Aligned w ∧ CarrierState (rest initial h) (holders.owners++loans) w ∧ StableRx (rest initial h) w) ∧
        HolderAccount temporary w ∧ Support sessions locals active w) ∧ (drained=true → ColdHead pid w))
    simp only [Bool.false_eq_true,ite_false]
    apply stop_bind (unsupported _) (fun _=>⟨_,rfl⟩)

theorem poll (initial : Ledger) (loans : Reservations) (pid budget : Nat) :
    PrefixPreserves (KeyBoundary sessions locals active temporary initial loans) (fun _=>True)
      (RxJoint.poll pid budget) := by
  change PrefixEnsures (KeyBoundary sessions locals active temporary initial loans) (fun _=>True) _
    (fun _=>KeyBoundary sessions locals active temporary initial loans)
  unfold RxJoint.poll
  apply stable_branch_bind (fun h w=>
    (∃holders:DurableHolders,holders.Aligned w ∧ CarrierState (rest initial h) (holders.owners++loans) w ∧ StableRx (rest initial h) w) ∧
      HolderAccount temporary w ∧ Support sessions locals active w)
  split
  · exact PrefixEnsures.pure (fun _ _ _=>True.intro) (fun _ _ hi=>hi)
  · apply PrefixEnsures.bind (Q:=KeyExit sessions locals active temporary initial loans pid)
    · apply PrefixEnsures.consequence (P:=KeyLoop sessions locals active temporary initial loans (0,({}:Gro),false))
        (Q:=KeyExit sessions locals active temporary initial loans pid) ?_
        (fun _ _ hi=>⟨hi,rfl⟩) (fun _ _ _ hi=>hi)
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      apply stable_forIn_exit _ _ _ (KeyLoop sessions locals active temporary initial loans)
        (KeyExit sessions locals active temporary initial loans pid)
        (fun _=>True) (fun _ _ _ _=>True.intro) (fun _ _ _ _=>True.intro)
        (fun _ _ _ hi=>⟨hi.1,fun bad=>by rw [hi.2] at bad; cases bad⟩)
      intro index acc
      rcases acc with ⟨n,g,drained⟩
      apply stable_assuming (drained=false)
      intro stopped
      subst drained
      apply PrefixEnsures.bind (peek_phase initial loans pid)
      intro first
      apply PrefixEnsures.bind (ready_phase initial loans pid first)
      intro go
      cases go with
      | false=>
        simp only [Bool.not_false,ite_true]
        exact PrefixEnsures.pure (fun _ _ _=>True.intro)
          (fun _ _ ⟨⟨holders,aligned,peek,stable,cold,_⟩,keys,support⟩=>
            ⟨⟨⟨holders,aligned,peek.1,stable⟩,keys,support⟩,fun _=>cold True.intro⟩)
      | true=>
        simp only [Bool.not_true,Bool.false_eq_true,ite_false]
        cases first with
        | none=>apply stop_bind (invariant _) (fun _=>⟨_,rfl⟩)
        | some id=>
          apply PrefixEnsures.bind ((capture_phase initial loans pid id).consequence
            (fun _ _ ⟨⟨holders,aligned,peek,stable,_,ready⟩,keys,support⟩=>
              ⟨⟨holders,aligned,peek,stable,ready True.intro⟩,keys,support⟩) (fun _ _ _ hi=>hi))
          intro captured
          rcases captured with ⟨pkt,stamp⟩
          apply PrefixEnsures.consequence (P:=fun h w=>
            WithKeys sessions locals active temporary
              (Accounted (fun ls h w=>Captured initial ls pid id (pkt,stamp) h w ∧ StableAt initial h w) loans) h w ∧ pkt.state≠.uncrypted)
            (Q:=_) ?_ (fun _ _ ⟨⟨holders,aligned,captured,stable,ready⟩,keys,support⟩=>
              ⟨⟨⟨holders,aligned,captured,stable⟩,keys,support⟩,ready⟩) (fun _ _ _ hi=>hi)
          apply stable_assuming (pkt.state≠.uncrypted)
          intro ready
          key_poll_step
    · intro acc
      exact poll_tail initial loans pid budget acc

theorem normal (pid budget : Nat)
    (funded : Boundary initial loans w.wg) (keys : HolderAccount temporary w.wg)
    (support : Support sessions locals active w.wg)
    (run : (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)).run w=.ok (result,v)) :
    HolderAccount temporary v.wg ∧ Support sessions locals active v.wg := by
  have empty : rest initial []=initial := by
    simp [rest,remaining,removedPackets,removedStamps]
  have entry : KeyBoundary sessions locals active temporary initial loans [] w := by
    obtain ⟨holders,funded,stable⟩ := funded
    refine ⟨⟨holders,funded.aligned,?_,?_⟩,keys,support⟩
    · simpa only [Ready,PollCarrier.Context,List.nil_append,empty] using funded.carriers
    · simpa only [StableAt,empty] using stable
  have observed := (poll_erases pid budget w []).trans run
  have post := (poll initial loans pid budget w [] entry).choose_spec.2.2
  rw [observed] at post
  exact post.2

end Leanux.Proofs.WG.RetirementSecurity.HolderPoll
