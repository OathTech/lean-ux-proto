import Leanux.Proofs.WG.Configuration.ConsumedRouting
import Leanux.Proofs.WG.AllowedIps.RoutingRxFrames
import Leanux.Proofs.WG.Queues.RxPollReceiptLink
import Leanux.Proofs.WG.Queues.RxPollCarrier

/-! The existing poll freezes routing at each actual consume entry. Its
concrete Stack callback is the original one; no new observer is introduced.
The local table is fixed only across this routing-preserving poll invocation. -/
namespace Leanux.Proofs.WG.RoutingPosition.Poll
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues AllowedIps RxJoint

def AtEntry (xs : FlatTable × FlatTable) : RxJoint.Event → Prop
  | .consumed _ _ _ r => GlobalRoutedView (routingView r.run.before) xs
  | _ => True

def Checks (xs : FlatTable × FlatTable) (h : List RxJoint.Event) : Prop :=
  ∀ e ∈ h, AtEntry xs e

def State (xs : FlatTable × FlatTable) (h : List RxJoint.Event) (w : World) : Prop :=
  GlobalRoutedView (routingView w.wg) xs ∧ Checks xs h

private theorem checks_append (ha : Checks xs a) (hb : Checks xs b) : Checks xs (a ++ b) := by
  intro e member
  exact (List.mem_append.mp member).elim (ha e) (hb e)

private theorem checks_emit (hh : Checks xs h) (he : AtEntry xs e) : Checks xs (h ++ [e]) :=
  checks_append hh (fun _ member => List.mem_singleton.mp member ▸ he)

private theorem routing_rule (a : Leanux.M α) (xs : FlatTable × FlatTable)
    (ha : ProductRetainsRoutingCall a) :
    Preserves (fun w : World => GlobalRoutedView (routingView w.wg) xs) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact hi.retains ((ProjectedAction.iff_run _ _ _).mp ha w x v hr)

/-- Arbitrary actual product access observers retain their full input domain. -/
private theorem access_rule (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (xs : FlatTable × FlatTable) (erases : ErasesPrefix g a) (frame : ProductRetainsRoutingCall a) :
    PrefixPreserves (State xs) (Checks xs) (access g) := by
  intro w h hi
  let suffix := ((runPrefix g w (h.filterMap accessEvent)).2.drop (h.filterMap accessEvent).length).map Event.access
  have hs : (runPrefix (access g) w h).2 = h ++ suffix := rfl
  have safe : Checks xs (runPrefix (access g) w h).2 := by
    rw [hs]
    apply checks_append hi.2
    intro e member
    obtain ⟨event,_,rfl⟩ := List.mem_map.mp member
    trivial
  refine ⟨suffix,hs,safe,?_⟩
  cases hr : (runPrefix (access g) w h).1 with
  | error stop => trivial
  | ok out => exact ⟨(hoare_iff_run _ _ _).mp (routing_rule a xs frame) w out.1 out.2 hi.1
      ((access_erases erases w h).symm.trans hr),safe⟩

private theorem native_access (g : MixedM α) (a : WG.M α) (xs : FlatTable × FlatTable)
    (erases : ErasesStatePrefix g a) (frame : RetainsRoutingCall a) :
    PrefixPreserves (State xs) (Checks xs) (access (liftWGObserver g)) :=
  access_rule _ _ xs (liftWGObserver_erases erases) frame.liftWG

private theorem lift_rule (a : Leanux.M α) (xs : FlatTable × FlatTable)
    (frame : ProductRetainsRoutingCall a) : PrefixPreserves (State xs) (Checks xs) (liftPrefix a) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.2)
  intro h w x v hi hr
  exact ⟨(hoare_iff_run _ _ _).mp (routing_rule a xs frame) w x v hi.1 hr,hi.2⟩

private theorem ambient_rule (a : AmbientM α) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (liftPrefix (monadLift a)) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.2)
  intro h w x v hi hr
  exact ⟨(hoare_iff_run _ _ _).mp
    (productAmbient_spec a (fun w : World => GlobalRoutedView (routingView w.wg) xs)
      (fun _ _ hp => hp)) w x v hi.1 hr,hi.2⟩

private theorem emit_rule (e : RxJoint.Event) (xs : FlatTable × FlatTable)
    (quiet : AtEntry xs e) : PrefixPreserves (State xs) (Checks xs) (emitPrefix e) := by
  intro w h hi
  have safe := checks_emit hi.2 quiet
  exact ⟨[e],rfl,safe,hi.1,safe⟩

private theorem receipt_rule (g : Obs α) (event : RunWitness α → RxJoint.Event)
    (xs : FlatTable × FlatTable) (hg : PrefixPreserves (State xs) (Checks xs) g)
    (quiet : ∀ r, AtEntry xs (event r)) :
    PrefixPreserves (State xs) (Checks xs) (receiptObserved g event) := by
  unfold receiptObserved
  exact hg.captureObserved.bind (fun r => (emit_rule _ xs (quiet r)).bind
    (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _))

private theorem capture_rule (id : SkbId) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (capture id) := by
  intro w h hi
  rw [capture_run]
  cases hr : (liftWG (getRxSkb id)).run w with
  | error stop => exact ⟨[],by simp,hi.2,True.intro⟩
  | ok out =>
    rcases out with ⟨pkt,v⟩
    have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
      (getRxSkb id) w v pkt hr
    obtain ⟨same,_,_,_,_⟩ := Packets.getRxSkb_current id w.wg v.wg pkt w.ambient v.ambient native
    have safe := checks_emit hi.2 (show AtEntry xs (.access (.packet (.read (.inr id) (packetStamp w.wg id)))) from True.intro)
    exact ⟨[_],rfl,safe,same ▸ hi.1,safe⟩

private theorem drop_rule (pid n id : Nat) (stamp : PacketStamp) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (drop pid n id stamp) := by
  unfold drop
  exact (native_access _ _ xs (rxDropPeekedPrefix_erases pid)
    (ProjectedRetainsRoutingCall.of_same
      ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingRxFrames.«0».Leanux.Proofs.WG.AllowedIps.dropRxQueue_routing) pid))).bind
    (fun _ => emit_rule _ xs True.intro)

private theorem consume_rule (pid n id : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (ep : Endpoint) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (consume pid n id stamp pkt ep) := by
  intro w h hi
  obtain ⟨s,hs,safe,normal⟩ := native_access _ _ xs (consumeDataDonePrefix_erases pid pkt ep)
    (consumeDataDone_routing pid pkt ep) w h hi
  rw [consume_run]
  cases hr : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t =>
    simp only [hr] at hs safe normal
    cases result with
    | error stop => exact ⟨s,hs,safe,True.intro⟩
    | ok out =>
      rcases out with ⟨returned,v⟩
      let receipt : RxDisposition.ConsumeReceipt := ⟨pid,pkt,ep,⟨returned,w.wg,v.wg,w.ambient,v.ambient⟩⟩
      have captured : Checks xs (t ++ [.consumed n id stamp receipt]) := checks_emit safe hi.1
      cases returned with
      | none => exact ⟨s ++ [_],by simp only [hs,List.append_assoc]; rfl,captured,normal.1,captured⟩
      | some bytes =>
        let entry : RxJoint.Entry := ⟨⟨n,id,bytes⟩,stamp,some receipt⟩
        have buffered := checks_emit captured (show AtEntry xs (.buffered entry) from True.intro)
        exact ⟨s ++ [_,_],by simp only [hs,List.append_assoc]; rfl,buffered,normal.1,buffered⟩

private theorem enter_rule (e : RxJoint.Entry) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (enter e) := by
  unfold enter
  exact (emit_rule (.entered e) xs True.intro).bind (fun _ => receipt_rule _ _ xs
    (access_rule _ _ xs (stackReceivePrefix_erases e.tag.bytes) (deliverInner_routing e.tag.bytes)) (fun _ => True.intro))

private theorem flush_rule (es : List RxJoint.Entry) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (flush es) :=
  PrefixPreserves.forM es enter (fun _ _ hi => hi.2) (fun e => enter_rule e xs)

private theorem normalList_rule (g : Gro) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (normalList g) := by
  unfold normalList
  split
  · exact PrefixPreserves.pure (fun _ _ hi => hi.2) _
  · exact (flush_rule _ xs).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _)

private theorem normalOne_rule (g : Gro) (e : RxJoint.Entry) (n : Nat) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (normalOne g e n) := by
  unfold normalOne
  dsimp only
  split
  · exact normalList_rule _ xs
  · exact PrefixPreserves.pure (fun _ _ hi => hi.2) _

private theorem receive_rule (g : Gro) (e : RxJoint.Entry) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (receive g e) := by
  have safe : ∀ h w, State xs h w → Checks xs h := fun _ _ hi => hi.2
  have stopped {α : Type} (message : String) :
      PrefixPreserves (State xs) (Checks xs) (liftPrefix (unsupported message : Leanux.M α)) := by
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ safe
    intro h w x v hi hr
    change (Except.error _ : Except Stop _) = _ at hr
    cases hr
  unfold receive
  repeat' first
    | exact normalOne_rule _ _ _ xs
    | exact stopped _
    | exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

private theorem flushAll_rule (g : Gro) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (flushAll g) := by
  unfold flushAll
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn
    · exact fun _ _ hi => hi.2
    · intro e g
      exact (normalOne_rule g e 1 xs).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  · intro g
    exact (normalList_rule {g with held := []} xs).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _)

private theorem ready_rule (first : Option SkbId) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (access (liftWGObserver (readyAccess first))) := by
  apply native_access _ _ xs (readyAccess_erases first)
  apply ProjectedRetainsRoutingCall.of_same
  have packets {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
    intro initial
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa only [id_eq,routingView,hd,Option.map_some,routingState] using hi
  routing_handshake_source [WG.andM,getRxSkb] using [packets]

private theorem state_rule (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs)
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState n id stamp pkt)) :=
  receipt_rule _ _ xs (ambient_rule (AmbientM.branch .rxPollNotCrypted (pkt.state != .crypted)) xs)
    (fun _ => True.intro)

private theorem counter_rule (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs)
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (Event.checkedCounter n id stamp pkt)) :=
  receipt_rule _ _ xs (native_access _ _ xs (counterValidatePrefix_erases _ _)
    (ProjectedRetainsRoutingCall.of_same (counterValidate_routing _ _))) (fun _ => True.intro)

private theorem endpoint_rule (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs)
      (receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source))) (Event.checkedEndpoint n id stamp pkt)) :=
  receipt_rule _ _ xs (lift_rule _ xs (RetainsRoutingCall.liftWG
    (show RetainsRoutingCall (endpointFromSkb pkt.source) from
      ProjectedRetainsRoutingCall.of_same
        (routing_kernel (project := _root_.id) _ (endpointFromSkb_sameWGStore pkt.source)))))
    (fun _ => True.intro)

private theorem free_rule (id : SkbId) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (access (liftWGObserver (freeRxSkbPrefix id))) := by
  apply native_access _ _ xs (freeRxSkbPrefix_erases id)
  apply ProjectedRetainsRoutingCall.of_same
  intro initial
  apply hoare_liftSkb (SkbStore.freeRx id)
  intro w d store hi hd
  simpa only [id_eq,routingView,hd,Option.map_some,routingState] using hi

private theorem peek_rule (pid : PeerId) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (access (liftWGObserver (peekAccess pid))) := by
  apply native_access _ (peekRxQueue pid) xs (peekAccess_erases pid)
  exact ProjectedRetainsRoutingCall.of_same
    ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingRxFrames.«0».Leanux.Proofs.WG.AllowedIps.peekRxQueue_routing) pid)

private theorem complete_rule (pid : PeerId) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (access (liftWGObserver (completeAccess pid))) := by
  apply native_access _ (completeRxQueue pid) xs (completeAccess_erases pid)
  exact ProjectedRetainsRoutingCall.of_same
    ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingRxFrames.«0».Leanux.Proofs.WG.AllowedIps.completeRxQueue_routing) pid)

private theorem keep_bind (g : Obs α) (f : α → Obs β) (xs : FlatTable × FlatTable)
    (hg : PrefixPreserves (State xs) (Checks xs) g)
    (hf : ∀ x, PrefixPreserves (State xs) (Checks xs) (f x)) :
    PrefixPreserves (State xs) (Checks xs) (g >>= f) := hg.bind hf

macro "routing_poll_check_step " xs:term : tactic => `(tactic| first
  | rx_phase_reduce
  | (rx_phase_head plain Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (rx_phase_head plain capture; apply keep_bind _ _ $xs (capture_rule _ $xs))
  | (rx_phase_head plain drop; apply keep_bind _ _ $xs (drop_rule _ _ _ _ $xs))
  | (rx_phase_head plain consume; apply keep_bind _ _ $xs (consume_rule _ _ _ _ _ _ $xs))
  | (rx_phase_head plain receive; apply keep_bind _ _ $xs (receive_rule _ _ $xs))
  | (rx_phase_head plain flushAll; apply keep_bind _ _ $xs (flushAll_rule _ $xs))
  | (rx_phase_head plain peekAccess; apply keep_bind _ _ $xs (peek_rule _ $xs))
  | (rx_phase_head plain readyAccess; apply keep_bind _ _ $xs (ready_rule _ $xs))
  | (rx_phase_head plain completeAccess; apply keep_bind _ _ $xs (complete_rule _ $xs))
  | (rx_phase_head receipt branch; apply keep_bind _ _ $xs (state_rule _ _ _ _ $xs))
  | (rx_phase_head receipt counterValidatePrefix; apply keep_bind _ _ $xs (counter_rule _ _ _ _ $xs))
  | (rx_phase_head receipt endpointFromSkb; apply keep_bind _ _ $xs (endpoint_rule _ _ _ _ $xs))
  | (rx_phase_head plain keypairPutPrefix; apply keep_bind _ _ $xs (native_access _ _ $xs
      (keypairPutPrefix_erases _ _) (ProjectedRetainsRoutingCall.of_same (keypairPut_routing _ _))))
  | (rx_phase_head plain peerPutMixed; apply keep_bind _ _ $xs (native_access _ _ $xs
      (peerPutMixed_erases _) (peerPut_retainsRouting _)))
  | (rx_phase_head plain freeRxSkbPrefix; apply keep_bind _ _ $xs (free_rule _ $xs))
  | (rx_phase_head plain branch; apply keep_bind _ _ $xs (ambient_rule (AmbientM.branch _ _) $xs))
  | (rx_phase_head plain invariant; apply keep_bind _ _ $xs (ambient_rule (AmbientM.invariant _) $xs))
  | (rx_phase_head plain unsupported; apply keep_bind _ _ $xs (ambient_rule (AmbientM.unsupported _) $xs))
  | (rx_phase_head plain ite; apply PrefixPreserves.ite)
  | rx_phase_intro
  | rx_phase_match)

/-- The actual fixed callback and all source guards are retained. Failed
prefixes keep every already captured entry, without an outgoing World. -/
theorem poll (pid : PeerId) (budget : Nat) (xs : FlatTable × FlatTable) :
    PrefixPreserves (State xs) (Checks xs) (RxJoint.poll pid budget) := by
  unfold RxJoint.poll
  repeat' first
    | exact fun _ _ hi => hi.2
    | routing_poll_check_step xs
    | (rx_phase_head plain ForIn.forIn
       apply keep_bind _ _ xs
       first | apply PrefixPreserves.range | apply PrefixPreserves.forIn)
    | exact And.right ‹State xs _ _›

/-- The per-poll seed has no old consumed receipts; arbitrary prior lifetime
entries are kept without asserting anything about earlier receipt values. -/
theorem poll_seed (pid : PeerId) (budget : Nat) (xs : FlatTable × FlatTable)
    (w : World) (prior : List LifetimeEvent)
    (hi : GlobalRoutedView (routingView w.wg) xs) :
    Checks xs (runPrefix (RxJoint.poll pid budget) w (seed prior)).2 := by
  have seeded : State xs (seed prior) w := by
    refine ⟨hi,?_⟩
    intro e member
    obtain ⟨event,_,rfl⟩ := List.mem_map.mp member
    trivial
  obtain ⟨_,_,safe,_⟩ := poll pid budget xs w (seed prior) seeded
  exact safe

/-- Exact same-result suffix for the existing RX observer, including Stop.
Every new consume entry has the table interpretation at this poll's entry. -/
theorem observePoll_entries (pid : PeerId) (budget : Nat) (xs : FlatTable × FlatTable)
    (w : World) (h : List RxHistory.Event)
    (hi : GlobalRoutedView (routingView w.wg) xs) :
    ∃ suffix,
      runPrefix (RxHistory.observePoll pid budget) w h =
        ((runPrefix (RxJoint.poll pid budget) w (seed (RxHistory.prior h))).1,
          h ++ suffix.map RxHistory.promote) ∧ Checks xs suffix := by
  obtain ⟨suffix,hs⟩ := poll_appends pid budget w (seed (RxHistory.prior h))
  refine ⟨suffix,RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl hs),?_⟩
  have checked := poll_seed pid budget xs w (RxHistory.prior h) hi
  rw [hs] at checked
  exact fun e member => checked e (List.mem_append_right _ member)

private theorem promoted_checks (hi : RoutingPosition.Inv initial h w)
    (checked : Checks (completionFold (h.filterMap RoutingJoint.routingEvent) initial) suffix) :
    RoutingPosition.Checks initial (h ++ suffix.map (fun e => RoutingJoint.Event.rx (RxHistory.promote e))) := by
  apply hi.2.append
  intro pre event post position
  have member : event ∈ suffix.map (fun e => RoutingJoint.Event.rx (RxHistory.promote e)) := by
    rw [position]
    simp
  obtain ⟨lower,hl,he⟩ := List.mem_map.mp member
  subst event
  cases lower <;> try trivial
  case consumed n skb saved receipt =>
    have noRouting : (pre ++ RoutingJoint.Event.rx (RxHistory.promote (.consumed n skb saved receipt)) :: post).filterMap
        RoutingJoint.routingEvent = [] := by
      rw [← position]
      exact filterMap_disjoint _ _ (fun _ => rfl) _
    have projectedPrefix : pre.filterMap RoutingJoint.routingEvent = [] := by
      simp only [List.filterMap_append,List.filterMap_cons,RoutingJoint.routingEvent] at noRouting
      exact (List.append_eq_nil_iff.mp noRouting).1
    change GlobalCompletionState initial ((h ++ pre).filterMap RoutingJoint.routingEvent) receipt.run.before
    simp only [List.filterMap_append,projectedPrefix,List.append_nil]
    exact ⟨hi.1.1,checked _ hl⟩

/-- Actual poll lifting preserves the positional joint invariant on every
normal return, and its exact reached checks on Stops. The RX and routing
facts refer to the same original joint observer invocation. -/
theorem observePoll (initial : FlatTable × FlatTable) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (RoutingPosition.Inv initial) (RoutingPosition.Safe initial)
      (RoutingJoint.rxAction (RxHistory.observePoll pid budget)) := by
  apply RoutingPosition.combine initial _ _ (Appends.focus _ _ _)
    (RoutingJoint.rxAction_routing (RxHistory.observePoll_erases pid budget))
    (global_completion_lift World.wg initial _ (actualRxPoll_routing pid budget))
  intro w h hi
  obtain ⟨suffix,hs,checked⟩ := observePoll_entries pid budget _ w (h.filterMap RoutingJoint.rxEvent) hi.1.2
  have focused := focusPrefix_suffix RoutingJoint.Event.rx RoutingJoint.rxEvent
    (RxHistory.observePoll pid budget) w h _ (suffix.map RxHistory.promote) hs
  change RoutingPosition.Checks initial
    (runPrefix (focusPrefix RoutingJoint.Event.rx RoutingJoint.rxEvent (RxHistory.observePoll pid budget)) w h).2
  rw [focused]
  simpa only [List.map_map,Function.comp_def] using promoted_checks hi checked

end Leanux.Proofs.WG.RoutingPosition.Poll
