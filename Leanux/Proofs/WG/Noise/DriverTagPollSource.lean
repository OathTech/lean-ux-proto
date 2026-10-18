import Leanux.Proofs.WG.Noise.DriverTagPollFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Poll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Silent

/-- An exact old observer transports a history-independent normal-state
contract. The only journal claim here is append-only growth, including Stops. -/
theorem quiet {E α : Type} (entry : TagMap) (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erase : ErasesPrefix g a)
    (keep : Preserves (ProductRetained entry) a) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,append⟩ := appends w h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    exact (hoare_iff_run _ _ _).mp keep w out.1 out.2 hi
      ((erase w h).symm.trans run)

theorem original {E α : Type} (entry : TagMap) (g : PrefixM E α) (a : Leanux.M α)
    (erase : ErasesPrefix g a)
    (keep : PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) g) :
    Preserves (ProductRetained entry) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  obtain ⟨_,_,_,normal⟩ := keep w [] hi
  have observed := (erase w []).trans run
  simpa only [observed] using normal

theorem joint_access {α : Type} (entry : TagMap)
    (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erase : ErasesPrefix g a) (keep : Preserves (ProductRetained entry) a) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) (RxJoint.access g) :=
  quiet entry _ a (RxJoint.access_appends g) (RxJoint.access_erases erase) keep

theorem joint_native {α : Type} (entry : TagMap) (g : MixedM α) (a : WG.M α)
    (erase : ErasesStatePrefix g a) (keep : Preserves (Retained entry) a) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True)
      (RxJoint.access (liftWGObserver g)) :=
  joint_access entry _ _ (liftWGObserver_erases erase)
    (PublicationPoll.native_product _ _ keep)

theorem lifted {E α : Type} (entry : TagMap) (a : Leanux.M α)
    (keep : Preserves (ProductRetained entry) a) :
    PrefixPreserves (fun (_ : List E) => ProductRetained entry) (fun _ => True) (liftPrefix a) :=
  PrefixEnsures.lift a (fun _ _ _ => True.intro)
    (fun _ w x v hi run => (hoare_iff_run _ _ _).mp keep w x v hi run)

theorem ambient {E α : Type} (entry : TagMap) (a : AmbientM α) :
    PrefixPreserves (fun (_ : List E) => ProductRetained entry) (fun _ => True)
      (liftPrefix (liftAmbient a)) :=
  lifted entry _ (productAmbient_spec a _ (fun _ _ hi => hi))

theorem emitted {E : Type} (entry : TagMap) (e : E) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) (emitPrefix e) :=
  RxJoint.GroSource.emit_preserves (fun _ _ _ => True.intro) e (fun _ _ hi => hi)

theorem receipt {α : Type} (entry : TagMap) (a : RxJoint.Obs α)
    (event : RunWitness α → RxJoint.Event)
    (keep : PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) a) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) (receiptObserved a event) :=
  RxJoint.GroSource.receipt_preserves (fun _ _ _ => True.intro) a event keep
    (fun _ _ _ _ _ _ _ hi => hi)

theorem capture (entry : TagMap) (skb : SkbId) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) (RxJoint.capture skb) := by
  intro w h hi
  obtain ⟨suffix,append⟩ := RxJoint.capture_appends skb w h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run : (runPrefix (RxJoint.capture skb) w h).1 with
  | error stop => trivial
  | ok out =>
    rcases out with ⟨⟨pkt,stamp⟩,v⟩
    have same := (RxDisposition.capture_selected skb w v h pkt stamp run).1
    simpa only [same] using hi

theorem consume (entry : TagMap) (pid occurrence id : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True)
      (RxJoint.consume pid occurrence id stamp pkt ep) := by
  intro w h hi
  obtain ⟨suffix,append⟩ := RxJoint.consume_appends pid occurrence id stamp pkt ep w h
  refine ⟨suffix,append,True.intro,?_⟩
  have keep := joint_native entry _ _ (consumeDataDonePrefix_erases pid pkt ep)
    (consumeDataDone_retained entry pid pkt ep) w h hi
  rw [RxJoint.consume_run]
  cases run : runPrefix (RxJoint.access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t =>
    obtain ⟨_,_,_,normal⟩ := keep
    simp only [run] at normal
    cases result with
    | error stop => trivial
    | ok result =>
      rcases result with ⟨out,v⟩
      cases out <;> exact normal

theorem gro_receive (entry : TagMap)
    (g : RxJoint.Gro) (e : RxJoint.Entry) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) (RxJoint.receive g e) := by
  rw [RxJoint.GroSource.receive_factor]
  apply RxJoint.GroSource.receive_preserves id _ (fun _ _ _ => True.intro)
  · intro e h w hi; exact hi
  · intro bytes
    exact joint_access entry _ _ (stackReceivePrefix_erases bytes) (Stack.native entry bytes)
  · intro e w h x v t _ _ hi; exact hi

theorem gro_flush (entry : TagMap)
    (g : RxJoint.Gro) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) (RxJoint.flushAll g) := by
  rw [RxJoint.GroSource.flushAll_factor]
  apply RxJoint.GroSource.flushAll_preserves id _ (fun _ _ _ => True.intro)
  · intro e h w hi; exact hi
  · intro bytes
    exact joint_access entry _ _ (stackReceivePrefix_erases bytes) (Stack.native entry bytes)
  · intro e w h x v t _ _ hi; exact hi

theorem poll_observed (entry : TagMap)
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) (RxJoint.poll pid budget) := by
  rw [RxJoint.PollSource.poll_factor]
  apply RxJoint.PollSource.poll_preserves (fun {_} a => a) _ _ (fun _ _ _ => True.intro)
  · intro peer
    exact joint_native entry _ _ (RxJoint.peekAccess_erases peer) (peek_retained entry peer)
  · intro first
    exact joint_native entry _ _ (RxJoint.readyAccess_erases first) (ready_retained entry first)
  · exact capture entry
  · intro peer n skb stamp
    unfold RxJoint.drop
    exact (joint_native entry _ _ (rxDropPeekedPrefix_erases peer) (drop_retained entry peer)).bind
      (fun _ => emitted entry _)
  · intro n skb stamp pkt
    exact receipt entry _ _ (ambient entry (AmbientM.branch .rxPollNotCrypted (pkt.state != .crypted)))
  · intro n skb stamp pkt
    exact receipt entry _ _ (joint_native entry _ _
      (counterValidatePrefix_erases pkt.keypair pkt.nonce) (counter_retained entry pkt.keypair pkt.nonce))
  · intro n skb stamp pkt
    exact receipt entry _ _ (lifted entry _
      (PublicationPoll.native_product _ _
        (of_frame entry _ (store_frame (endpointFromSkb_sameWGStore pkt.source)))))
  · exact consume entry
  · intro kid
    exact joint_native entry _ _ (keypairPutPrefix_erases (some kid) false) (Silent.keypairPut entry (some kid) false)
  · intro peer
    exact joint_native entry _ _ (peerPutMixed_erases (some peer)) (Silent.peerPut entry (some peer))
  · intro skb
    exact joint_native entry _ _ (freeRxSkbPrefix_erases skb)
      (of_frame entry _ (packet_frame (SkbStore.freeRx skb)))
  · intro peer
    exact joint_native entry _ _ (RxJoint.completeAccess_erases peer) (complete_retained entry peer)
  · intro b; exact ambient entry (AmbientM.branch .rxPollNoBudget b)
  · intro b; exact ambient entry (AmbientM.branch .rxPollCounterInvalid b)
  · intro b; exact ambient entry (AmbientM.branch .rxPollEndpointFailed b)
  · intro b; exact ambient entry (AmbientM.branch .rxPollFree b)
  · intro b; exact ambient entry (AmbientM.branch .rxPollBudgetDone b)
  · intro b; exact ambient entry (AmbientM.branch .rxPollComplete b)
  · exact gro_receive entry
  · exact gro_flush entry

/-- Original poll with the real inner-packet delivery callback. No successful
completion, residency, queue readiness, or caller-supplied frame is assumed. -/
theorem poll_native (entry : TagMap)
    (pid : PeerId) (budget : Nat) :
    Preserves (ProductRetained entry)
      (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) :=
  original entry _ _ (RxJoint.poll_erases pid budget) (poll_observed entry pid budget)

theorem history_poll (entry : TagMap)
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) (RxHistory.observePoll pid budget) :=
  quiet entry _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (poll_native entry pid budget)

theorem history_native {α : Type} (entry : TagMap) (g : MixedM α) (a : WG.M α)
    (erase : ErasesStatePrefix g a) (keep : Preserves (Retained entry) a) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True)
      (RxHistory.audit (auditFocus (liftWGObserver g))) :=
  quiet entry _ _ (Appends.focus _ _ _)
    (RxHistory.audit_erases (auditFocus_erases (liftWGObserver_erases erase)))
    (PublicationPoll.native_product _ _ keep)

theorem pending_scan (entry : TagMap) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True)
      (RxHistory.audit (auditFocus (liftWGObserver RxNapi.pendingPrefix))) := by
  apply history_native entry _ _ RxNapi.pending_erases
  apply of_frame
  apply store_frame
  unfold RxNapi.pendingSource
  exact getDev_sameWGStore.bind (fun _ => SameView.pure _ _)

theorem scheduled_scan (entry : TagMap) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True)
      (RxHistory.audit (auditFocus (liftWGObserver RxNapi.scheduledPrefix))) := by
  apply history_native entry _ _ RxNapi.scheduled_erases
  apply of_frame
  apply store_frame
  unfold RxNapi.scheduledSource
  exact getDev_sameWGStore.bind (fun _ => SameView.pure _ _)


theorem softirq_observed (entry : TagMap) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) RxHistory.napiSoftirq := by
  rw [NapiSource.softirq_factor]
  exact RxNapi.softirq_preserves (fun _ _ _ => True.intro) (fun _ => product_store entry)
    (pending_scan entry) (history_poll entry)

theorem inline_observed (entry : TagMap) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) RxHistory.pollScheduledInline := by
  rw [NapiSource.inline_factor]
  exact RxNapi.inline_preserves (fun _ _ _ => True.intro) (fun _ => product_store entry)
    (pending_scan entry) (history_poll entry)

theorem irqExit_observed (entry : TagMap) :
    PrefixPreserves (fun _ => ProductRetained entry) (fun _ => True) RxHistory.napiIrqExit := by
  rw [NapiSource.irqExit_factor]
  exact RxNapi.irqExit_preserves (fun _ _ _ => True.intro) (fun _ => product_store entry)
    (scheduled_scan entry) (softirq_observed entry)

theorem softirq_native (entry : TagMap) :
    Preserves (ProductRetained entry) Leanux.Env.napiSoftirq :=
  original entry _ _ RxHistory.napiSoftirq_erases (softirq_observed entry)

theorem inline_native (entry : TagMap) :
    Preserves (ProductRetained entry) Leanux.Env.pollScheduledInline :=
  original entry _ _ RxHistory.pollScheduledInline_erases (inline_observed entry)

theorem irqExit_native (entry : TagMap) :
    Preserves (ProductRetained entry) Leanux.Env.napiIrqExit :=
  original entry _ _ RxHistory.napiIrqExit_erases (irqExit_observed entry)

end Leanux.Proofs.WG.Noise.DriverTags.Poll
