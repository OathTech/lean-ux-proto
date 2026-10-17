import Leanux.Proofs.WG.Queues.RxStableObserved

/-! Stable poll iteration composition, retaining exact source checks and the
original partial outcomes. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
open RxJoint PollCarrier

private theorem counter_napi (kid : KeypairId) (nonce : Nat) (initial) :
    Preserves (NapiFrames.Retained initial) (counterValidate kid nonce) := by
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,
    Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' napi_step initial

theorem stable_counterValidate (kid : KeypairId) (nonce : Nat) (hs : StableRx cs w)
    (a b : Ambient) (hr : ((counterValidate kid nonce).run w).run a = .ok ((result,v),b)) :
    StableRx cs v := by
  apply hs.retains
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp (RxRing.counterValidate_cell kid nonce) w a result v b hr
  · exact congrArg (fun s => s.2.1)
      ((ProjectedAction.iff_run_ambient _ _ _).mp (counter_carrierView kid nonce) w a result v b hr)
  · have exactQueues := (ProjectedAction.iff_run_ambient _ _ _).mp (counterValidate_rxQueues kid nonce) w a result v b hr
    rw [exactQueues]
    exact rx_retained_refl _
  · exact (hoare_iff_run_ambient _ _ _).mp (counter_napi kid nonce (NapiFrames.napiView w))
      w a result v b (NapiFrames.refl w) hr

private theorem product_stable (a : Leanux.M α) (frame : SameProductStore a)
    (hs : StableRx cs w.wg) (hr : a.run w = .ok (result,v)) : StableRx cs v.wg := by
  apply hs.view
  exact (ProjectedAction.iff_run _ _ _).mp
    (stableView_kernel (project := World.wg) (frame.factor (fun s : ProductStore43 => s.2.2.2))) w result v hr

theorem stable_lift_observed (a : Leanux.M α) (frame : SameProductStore a)
    (old : PrefixPreserves P (fun _ => True) (liftPrefix a)) :
    PrefixPreserves (fun h w => P h w ∧ StableAt initial h w) (fun _ => True) (liftPrefix a) := by
  apply stable_observed _ a id (Appends.lift _) (erasesPrefix_lift _).to_projected
    (HistoryFrame.lift _ _) old
  intro w h x v _ hs hr
  exact product_stable a frame hs hr

theorem stable_receipt_lift_observed (a : Leanux.M α) (frame : SameProductStore a)
    (f : RunWitness α → RxJoint.Event) (hf : ∀r,removedStamp (f r) = none)
    (old : PrefixPreserves P (fun _ => True) (receiptObserved (liftPrefix a) f)) :
    PrefixPreserves (fun h w => P h w ∧ StableAt initial h w) (fun _ => True)
      (receiptObserved (liftPrefix a) f) := by
  apply stable_observed _ a id (Appends.lift _).receiptObserved
    (RxLink.receipt_erases (erasesPrefix_lift _)).to_projected
    ((HistoryFrame.lift _ _).receiptObserved hf) old
  intro w h x v _ hs hr
  exact product_stable a frame hs hr

theorem stable_live_counter (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (fun h w => Live initial loans pid skb stamp pkt h w ∧ StableAt initial h w)
      (fun _ => True)
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (RxJoint.Event.checkedCounter n skb stamp pkt)) := by
  apply stable_observed _ (liftWG (counterValidate pkt.keypair pkt.nonce)) id
    (access_appends _).receiptObserved
    (RxLink.receipt_erases (access_erases (liftWGObserver_erases (counterValidatePrefix_erases _ _)))).to_projected
    ((access_removed _).receiptObserved (fun _ => rfl)) (live_counter n skb stamp pkt)
  intro w h x v _ hs hr
  exact stable_counterValidate _ _ hs w.ambient v.ambient
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) _ w v x hr)

theorem stable_bare_option (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (g : Gro) (out : Option Entry) :
    PrefixPreserves (fun h w => Bare initial loans pid skb stamp h w ∧ StableAt initial h w)
      (fun _ => True)
      (forIn out.toList g (fun e cur => do let next ← receive cur e; pure (.yield next))) := by
  change PrefixEnsures (fun h w => Bare initial loans pid skb stamp h w ∧ StableRx (rest initial h) w.wg) (fun _ => True) _
    (fun _ h w => Bare initial loans pid skb stamp h w ∧ StableRx (rest initial h) w.wg)
  cases out with
  | none => exact PrefixEnsures.pure (fun _ _ _ => True.intro) (fun _ _ hi => hi)
  | some e =>
    simpa only [Option.toList_some,List.forIn_cons,List.forIn_nil,bind_assoc,pure_bind,bind_pure,PrefixPreserves,PrefixEnsures] using
      stable_receive_observed initial loans pid skb stamp g e

/-- A pure source fact is kept as a proof argument, rather than inferred from
a failed source call or from its eventual endpoint. -/
theorem stable_assuming (r : Prop) (a : Obs α)
    (hr : r → PrefixEnsures P (fun _ => True) a Q) :
    PrefixEnsures (fun h w => P h w ∧ r) (fun _ => True) a Q :=
  fun w h hi => hr hi.2 w h hi.1

theorem stable_cleanup_bind (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer = pid) (tail : Obs α)
    (next : PrefixEnsures (fun h w => Ready initial loans h w ∧ StableAt initial h w)
      (fun _ => True) tail Q) :
    PrefixEnsures (fun h w => Bare initial loans pid skb stamp h w ∧ StableAt initial h w)
      (fun _ => True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _ ← liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))
          tail) Q := by
  simpa only [bind_assoc,StableAt] using PrefixEnsures.bind
    (stable_cleanup_observed initial loans pid skb stamp pkt flag guard) (fun u => by cases u; exact next)

theorem stable_cleanup_live_bind (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (flag : Bool) (guard : pkt.peer = pid) (tail : Obs α)
    (next : PrefixEnsures (fun h w => Ready initial loans h w ∧ StableAt initial h w)
      (fun _ => True) tail Q) :
    PrefixEnsures (fun h w => Live initial loans pid skb stamp pkt h w ∧ StableAt initial h w)
      (fun _ => True)
      (do access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
          access (liftWGObserver (peerPutMixed (some pid)))
          _ ← liftPrefix (branch .rxPollFree flag)
          access (liftWGObserver (freeRxSkbPrefix skb))
          tail) Q :=
  (stable_cleanup_bind initial loans pid skb stamp pkt flag guard tail next).consequence
    (fun _ _ hi => ⟨hi.1.1,hi.2⟩) (fun _ _ _ hi => hi)

/-- The recorded Boolean is the source Boolean. This rule exposes it without
forgetting its value, and preserves the exact recorded Ambient state. -/
theorem stable_branch_bind (P : List RxJoint.Event → WGWorld → Prop)
    (d : Decision) (b : Bool) (f : Bool → Obs α)
    (hf : PrefixEnsures (fun h w => P h w.wg) (fun _ => True) (f b) Q) :
    PrefixEnsures (fun h w => P h w.wg) (fun _ => True) (liftPrefix (branch d b) >>= f) Q := by
  intro w h hi
  have branchRun : (branch d b : Leanux.M Bool).run w =
      .ok (b,{w with ambient := CounterWindow.record w.ambient d b}) := rfl
  simpa only [runPrefix_bind,runPrefix_lift,branchRun] using
    hf {w with ambient := CounterWindow.record w.ambient d b} h hi

end Leanux.Proofs.WG.Queues.RxCredits
