import Leanux.Proofs.WG.Noise.PendingPollFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues ConfiguredRemoval

theorem joint_safe (seen : List Nat) (h : List RxJoint.Event) (w : World)
    (hi : JointInv seen h w) : JointSafe seen h := hi.2.2.distinct

theorem joint_quiet {α : Type} (seen : List Nat) (g : RxJoint.Obs α) (a : Leanux.M α)
    (appends : Appends g) (erase : ErasesPrefix g a)
    (labels : ∀ w h, jointLabels (runPrefix g w h).2 = jointLabels h)
    (keep : ∀ seen, Preserves (fun w : World => NativeInv w.wg seen) a) :
    PrefixPreserves (JointInv seen) (JointSafe seen) g := by
  intro w h hi
  obtain ⟨suffix,append⟩ := appends w h
  have same := labels w h
  have safe : JointSafe seen (runPrefix g w h).2 := by
    change ((jointLabels _).reverse ++ seen).Nodup
    rw [same]
    exact hi.2.2.distinct
  refine ⟨suffix,append,safe,?_⟩
  cases run : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    have final := (hoare_iff_run _ _ _).mp (keep _) w out.1 out.2 hi ((erase w h).symm.trans run)
    change NativeInv out.2.wg ((jointLabels _).reverse ++ seen)
    rw [same]
    exact final

theorem joint_access {α : Type} (seen : List Nat) (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erase : ErasesPrefix g a)
    (keep : ∀ seen, Preserves (fun w : World => NativeInv w.wg seen) a) :
    PrefixPreserves (JointInv seen) (JointSafe seen) (RxJoint.access g) :=
  joint_quiet seen _ a (RxJoint.access_appends g) (RxJoint.access_erases erase) (access_labels g) keep

theorem joint_native {α : Type} (seen : List Nat) (g : MixedM α) (a : WG.M α)
    (erase : ErasesStatePrefix g a) (keep : NativeKeeps a) :
    PrefixPreserves (JointInv seen) (JointSafe seen) (RxJoint.access (liftWGObserver g)) :=
  joint_access seen _ _ (liftWGObserver_erases erase)
    (fun prior => PublicationPoll.native_product _ _ (keep prior))

theorem joint_lift {α : Type} (seen : List Nat) (a : Leanux.M α)
    (keep : ∀ prior, Preserves (fun w : World => NativeInv w.wg prior) a) :
    PrefixPreserves (JointInv seen) (JointSafe seen) (liftPrefix a) :=
  PrefixEnsures.lift a (joint_safe seen)
    (fun _ w x v hi run => (hoare_iff_run _ _ _).mp (keep _) w x v hi run)

theorem joint_ambient {α : Type} (seen : List Nat) (a : AmbientM α) :
    PrefixPreserves (JointInv seen) (JointSafe seen) (liftPrefix (liftAmbient a)) :=
  joint_lift seen _ (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))

theorem quiet_event (seen : List Nat) (e : RxJoint.Event)
    (quiet : CounterConsume.eventLabel (RxHistory.promote e) = none)
    (h : List RxJoint.Event) (w : World) (hi : JointInv seen h w) :
    JointInv seen (h ++ [e]) w := by
  change NativeInv w.wg ((jointLabels _).reverse ++ seen)
  have labels : jointLabels (h ++ [e]) = jointLabels h := by
    simp only [jointLabels,CounterConsume.confirmationLabels,List.map_append,
      List.map_cons,List.map_nil,List.filterMap_append,List.filterMap_cons,
      quiet,List.filterMap_nil,List.append_nil]
  rw [labels]
  exact hi

theorem joint_emit (seen : List Nat) (e : RxJoint.Event)
    (quiet : CounterConsume.eventLabel (RxHistory.promote e) = none) :
    PrefixPreserves (JointInv seen) (JointSafe seen) (emitPrefix e) :=
  RxJoint.GroSource.emit_preserves (joint_safe seen) e (quiet_event seen e quiet)

theorem joint_receipt {α : Type} (seen : List Nat) (a : RxJoint.Obs α)
    (event : RunWitness α → RxJoint.Event)
    (keep : PrefixPreserves (JointInv seen) (JointSafe seen) a)
    (quiet : ∀ r, CounterConsume.eventLabel (RxHistory.promote (event r)) = none) :
    PrefixPreserves (JointInv seen) (JointSafe seen) (receiptObserved a event) :=
  RxJoint.GroSource.receipt_preserves (joint_safe seen) a event keep
    (fun _ _ _ _ _ _ _ hi => quiet_event seen _ (quiet _) _ _ hi)

/-- The actual packet capture keeps pending allocation identities and all
earlier confirmation labels while appending only its lifetime accesses. -/
theorem joint_capture (seen : List Nat) (skb : SkbId) :
    PrefixPreserves (JointInv seen) (JointSafe seen) (RxJoint.capture skb) := by
  intro w h hi
  obtain ⟨suffix,append⟩ := RxJoint.capture_appends skb w h
  have labels : jointLabels (runPrefix (RxJoint.capture skb) w h).2 = jointLabels h :=
    access_labels (liftWGObserver (getRxSkbPrefix skb)) w h
  refine ⟨suffix,append,?_,?_⟩
  · change ((jointLabels _).reverse ++ seen).Nodup
    rw [labels]
    exact hi.2.2.distinct
  · cases run : (runPrefix (RxJoint.capture skb) w h).1 with
    | error stop => trivial
    | ok out =>
      rcases out with ⟨⟨pkt,stamp⟩,v⟩
      have same := (RxDisposition.capture_selected skb w v h pkt stamp run).1
      change NativeInv v.wg ((jointLabels _).reverse ++ seen)
      rw [labels,same]
      exact hi

theorem joint_gro_receive (seen : List Nat)
    (stack : ∀ prior bytes, Preserves (fun w : World => NativeInv w.wg prior) (Leanux.Env.deliverInner bytes))
    (g : RxJoint.Gro) (e : RxJoint.Entry) :
    PrefixPreserves (JointInv seen) (JointSafe seen) (RxJoint.receive g e) := by
  rw [RxJoint.GroSource.receive_factor]
  apply RxJoint.GroSource.receive_preserves id _ (joint_safe seen)
  · intro e h w hi
    exact quiet_event seen _ rfl h w hi
  · intro bytes
    exact joint_access seen _ _ (stackReceivePrefix_erases bytes) (fun prior => stack prior bytes)
  · intro e w h x v t _ _ hi
    exact quiet_event seen _ rfl t v hi

theorem joint_gro_flush (seen : List Nat)
    (stack : ∀ prior bytes, Preserves (fun w : World => NativeInv w.wg prior) (Leanux.Env.deliverInner bytes))
    (g : RxJoint.Gro) :
    PrefixPreserves (JointInv seen) (JointSafe seen) (RxJoint.flushAll g) := by
  rw [RxJoint.GroSource.flushAll_factor]
  apply RxJoint.GroSource.flushAll_preserves id _ (joint_safe seen)
  · intro e h w hi
    exact quiet_event seen _ rfl h w hi
  · intro bytes
    exact joint_access seen _ _ (stackReceivePrefix_erases bytes) (fun prior => stack prior bytes)
  · intro e w h x v t _ _ hi
    exact quiet_event seen _ rfl t v hi

/-- The callback premise is about the exact original Stack function. All poll
atoms, consume receipts, GRO batching and stopped-prefix labels remain actual. -/
theorem joint_poll (seen : List Nat)
    (stack : ∀ prior bytes, Preserves (fun w : World => NativeInv w.wg prior) (Leanux.Env.deliverInner bytes))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (JointInv seen) (JointSafe seen) (RxJoint.poll pid budget) := by
  rw [RxJoint.PollSource.poll_factor]
  apply RxJoint.PollSource.poll_preserves (fun {_} a => a) _ _ (joint_safe seen)
  · intro peer
    exact joint_native seen _ _ (RxJoint.peekAccess_erases peer) (peek_keeps peer)
  · intro first
    exact joint_native seen _ _ (RxJoint.readyAccess_erases first) (ready_keeps first)
  · exact joint_capture seen
  · intro peer n skb stamp
    unfold RxJoint.drop
    exact (joint_native seen _ _ (rxDropPeekedPrefix_erases peer) (drop_keeps peer)).bind
      (fun _ => joint_emit seen _ rfl)
  · intro n skb stamp pkt
    exact joint_receipt seen _ _ (joint_ambient seen (AmbientM.branch .rxPollNotCrypted (pkt.state != .crypted))) (fun _ => rfl)
  · intro n skb stamp pkt
    exact joint_receipt seen _ _
      (joint_native seen _ _ (counterValidatePrefix_erases pkt.keypair pkt.nonce) (counter_keeps pkt.keypair pkt.nonce)) (fun _ => rfl)
  · intro n skb stamp pkt
    exact joint_receipt seen _ _ (joint_lift seen _
      (fun prior => PublicationPoll.native_product _ _
        (keeps_store _ (endpointFromSkb_sameWGStore pkt.source) prior))) (fun _ => rfl)
  · exact consume seen
  · intro kid
    exact joint_native seen _ _ (keypairPutPrefix_erases (some kid) false) (keypair_keeps (some kid) false)
  · intro peer
    exact joint_native seen _ _ (peerPutMixed_erases (some peer)) (peer_keeps (some peer))
  · intro skb
    exact joint_native seen _ _ (freeRxSkbPrefix_erases skb) (keeps_packet (SkbStore.freeRx skb))
  · intro peer
    exact joint_native seen _ _ (RxJoint.completeAccess_erases peer) (complete_keeps peer)
  · intro b; exact joint_ambient seen (AmbientM.branch .rxPollNoBudget b)
  · intro b; exact joint_ambient seen (AmbientM.branch .rxPollCounterInvalid b)
  · intro b; exact joint_ambient seen (AmbientM.branch .rxPollEndpointFailed b)
  · intro b; exact joint_ambient seen (AmbientM.branch .rxPollFree b)
  · intro b; exact joint_ambient seen (AmbientM.branch .rxPollBudgetDone b)
  · intro b; exact joint_ambient seen (AmbientM.branch .rxPollComplete b)
  · exact joint_gro_receive seen stack
  · exact joint_gro_flush seen stack

theorem joint_seed_labels (h : List LifetimeEvent) : jointLabels (RxJoint.seed h) = [] := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    simpa only [RxJoint.seed,List.map_cons,jointLabels,CounterConsume.confirmationLabels,
      List.filterMap_cons,RxHistory.promote,CounterConsume.eventLabel] using ih

theorem promoted_seen (h : List RxHistory.Event) (suffix : List RxJoint.Event) :
    (CounterConsume.confirmationLabels (h ++ suffix.map RxHistory.promote)).reverse =
      (jointLabels suffix).reverse ++ (CounterConsume.confirmationLabels h).reverse := by
  simp only [CounterConsume.confirmationLabels,List.filterMap_append,List.reverse_append,jointLabels]

/-- The exact seed/suffix boundary keeps all earlier global confirmation labels;
only new local events are promoted, in their original execution order. -/
theorem observed_poll
    (stack : ∀ prior bytes, Preserves (fun w : World => NativeInv w.wg prior) (Leanux.Env.deliverInner bytes))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves StateInv HistorySafe (RxHistory.observePoll pid budget) := by
  intro w h hi
  let initial := RxJoint.seed (RxHistory.prior h)
  let seen := (CounterConsume.confirmationLabels h).reverse
  have entered : JointInv seen initial w := by
    change NativeInv w.wg ((jointLabels initial).reverse ++ seen)
    rw [joint_seed_labels]
    exact hi
  obtain ⟨suffix,append,safe,normal⟩ := joint_poll seen stack pid budget w initial entered
  have labels : jointLabels (runPrefix (RxJoint.poll pid budget) w initial).2 = jointLabels suffix := by
    rw [append,jointLabels_append,joint_seed_labels,List.nil_append]
  have global := RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl append)
  rw [global]
  refine ⟨suffix.map RxHistory.promote,rfl,?_,?_⟩
  · change (CounterConsume.confirmationLabels (h ++ suffix.map RxHistory.promote)).reverse.Nodup
    rw [promoted_seen]
    change ((jointLabels _).reverse ++ seen).Nodup at safe
    rw [labels] at safe
    exact safe
  · cases run : (runPrefix (RxJoint.poll pid budget) w initial).1 with
    | error stop => trivial
    | ok out =>
      simp only [run] at normal
      change NativeInv out.2.wg (CounterConsume.confirmationLabels (h ++ suffix.map RxHistory.promote)).reverse
      rw [promoted_seen]
      change NativeInv out.2.wg ((jointLabels _).reverse ++ seen) at normal
      rw [labels] at normal
      exact normal

theorem audit_quiet_native {α : Type} (g : MixedM α) (a : WG.M α)
    (erase : ErasesStatePrefix g a) (keep : NativeKeeps a) :
    PrefixPreserves StateInv HistorySafe (RxHistory.audit (auditFocus (liftWGObserver g))) := by
  apply observer _ _ (Appends.focus _ _ _)
    (RxHistory.audit_erases (auditFocus_erases (liftWGObserver_erases erase)))
  · intro w h
    exact focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent
      CounterConsume.eventLabel (fun _ => rfl) _ w h
  · exact native_product a keep

theorem pending_scan : PrefixPreserves StateInv HistorySafe
    (RxHistory.audit (auditFocus (liftWGObserver RxNapi.pendingPrefix))) := by
  apply audit_quiet_native _ _ RxNapi.pending_erases
  apply keeps_store
  unfold RxNapi.pendingSource
  exact getDev_sameWGStore.bind (fun _ => SameView.pure _ _)

theorem scheduled_scan : PrefixPreserves StateInv HistorySafe
    (RxHistory.audit (auditFocus (liftWGObserver RxNapi.scheduledPrefix))) := by
  apply audit_quiet_native _ _ RxNapi.scheduled_erases
  apply keeps_store
  unfold RxNapi.scheduledSource
  exact getDev_sameWGStore.bind (fun _ => SameView.pure _ _)

theorem napi_softirq
    (stack : ∀ prior bytes, Preserves (fun w : World => NativeInv w.wg prior) (Leanux.Env.deliverInner bytes)) :
    PrefixPreserves StateInv HistorySafe RxHistory.napiSoftirq := by
  rw [NapiSource.softirq_factor]
  exact RxNapi.softirq_preserves (fun _ _ hi => hi.2.2.distinct) state_product_store
    pending_scan (observed_poll stack)

theorem napi_inline
    (stack : ∀ prior bytes, Preserves (fun w : World => NativeInv w.wg prior) (Leanux.Env.deliverInner bytes)) :
    PrefixPreserves StateInv HistorySafe RxHistory.pollScheduledInline := by
  rw [NapiSource.inline_factor]
  exact RxNapi.inline_preserves (fun _ _ hi => hi.2.2.distinct) state_product_store
    pending_scan (observed_poll stack)

theorem napi_irq_exit
    (stack : ∀ prior bytes, Preserves (fun w : World => NativeInv w.wg prior) (Leanux.Env.deliverInner bytes)) :
    PrefixPreserves StateInv HistorySafe RxHistory.napiIrqExit := by
  rw [NapiSource.irqExit_factor]
  exact RxNapi.irqExit_preserves (fun _ _ hi => hi.2.2.distinct) state_product_store
    scheduled_scan (napi_softirq stack)

end Leanux.Proofs.WG.Noise.PendingSession
