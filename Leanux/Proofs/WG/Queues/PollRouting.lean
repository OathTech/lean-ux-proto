import Leanux.Proofs.WG.Queues.RxPollHistory
import Leanux.Proofs.WG.AllowedIps.RoutingRxFrames

/-! Routing at reached consume cuts of the existing poll observer. The local
history premise certifies only actual consumed receipts; no lifetime, credit,
affiliation or allocation condition is required. -/
namespace Leanux.Proofs.WG.Queues.PollRouting
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.Lifetimes RxJoint

def receipt? : Event → Option RxDisposition.ConsumeReceipt
  | .consumed _ _ _ r => some r
  | _ => none

def Safe (xs : FlatTable × FlatTable) (h : List Event) : Prop :=
  ∀ r ∈ h.filterMap receipt?, RoutedView (routingView r.run.before) xs ∧ r.Valid

def Inv (xs : FlatTable × FlatTable) (h : List Event) (w : World) : Prop :=
  Safe xs h ∧ RoutedView (routingView w.wg) xs

private theorem quiet (xs : FlatTable × FlatTable) (g : Obs α)
    (ha : Appends g) (hm : HistoryFrame receipt? g)
    (keep : ∀ w h x v, RoutedView (routingView w.wg) xs →
      (runPrefix g w h).1 = .ok (x,v) → RoutedView (routingView v.wg) xs) :
    PrefixPreserves (Inv xs) (Safe xs) g := by
  intro w h hi
  obtain ⟨suffix,hs⟩ := ha w h
  have safe : Safe xs (runPrefix g w h).2 := by
    unfold Safe
    rw [hm w h]
    exact hi.1
  refine ⟨suffix,hs,safe,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact ⟨safe,keep w h out.1 out.2 hi.2 hr⟩

private theorem quiet_erases (xs : FlatTable × FlatTable) (g : Obs α)
    (ha : Appends g) (hm : HistoryFrame receipt? g) {a : Leanux.M α}
    (he : ErasesPrefix g a) (hr : ProductRetainsRoutingCall a) :
    PrefixPreserves (Inv xs) (Safe xs) g :=
  quiet xs g ha hm (fun w h x v hi normal => hi.retains
    ((ProjectedAction.iff_run _ _ _).mp hr w x v ((he w h).symm.trans normal)))

private theorem access_routing (xs : FlatTable × FlatTable) (g : PrefixM LifetimeEvent α)
    {a : Leanux.M α} (he : ErasesPrefix g a) (hr : ProductRetainsRoutingCall a) :
    PrefixPreserves (Inv xs) (Safe xs) (access g) :=
  quiet_erases xs _ (access_appends g)
    (fun w h => focusPrefix_other Event.access accessEvent receipt? (fun _ => rfl) g w h)
    (access_erases he) hr

private theorem native_access (xs : FlatTable × FlatTable) (g : MixedM α)
    {a : WG.M α} (he : ErasesStatePrefix g a) (hr : RetainsRoutingCall a) :
    PrefixPreserves (Inv xs) (Safe xs) (access (liftWGObserver g)) :=
  access_routing xs _ (liftWGObserver_erases he) hr.liftWG

private theorem lifted (xs : FlatTable × FlatTable) (a : Leanux.M α)
    (hr : ProductRetainsRoutingCall a) :
    PrefixPreserves (Inv xs) (Safe xs) (liftPrefix a) :=
  quiet_erases xs _ (Appends.lift a) (HistoryFrame.lift _ a) (erasesPrefix_lift a) hr

private theorem emit_quiet (xs : FlatTable × FlatTable) (e : Event) (he : receipt? e = none) :
    PrefixPreserves (Inv xs) (Safe xs) (emitPrefix e) := by
  apply quiet xs _ (emit_appends e) (HistoryFrame.emit e he)
  intro w h x v hi hr
  cases hr
  exact hi

private theorem receipt_quiet (xs : FlatTable × FlatTable) (a : Obs α)
    (ha : PrefixPreserves (Inv xs) (Safe xs) a)
    (f : RunWitness α → Event) (hf : ∀ r, receipt? (f r) = none) :
    PrefixPreserves (Inv xs) (Safe xs) (receiptObserved a f) := by
  unfold receiptObserved
  exact ha.captureObserved.bind (fun r =>
    (emit_quiet xs (f r) (hf r)).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.1) r.value))

/-- This is the real consume observer at its original incoming journal. Its
receipt obtains routing from this actual entry state, and validity from this
same normal execution. A stopped consume emits no synthetic receipt. -/
theorem consume (xs : FlatTable × FlatTable) (pid n skb : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (Inv xs) (Safe xs) (RxJoint.consume pid n skb stamp pkt ep) := by
  intro w h hi
  have lower := native_access xs (consumeDataDonePrefix pid pkt ep)
    (consumeDataDonePrefix_erases pid pkt ep) (consumeDataDone_routing pid pkt ep) w h hi
  obtain ⟨suffix,hs,hsafe,hnormal⟩ := lower
  have erased := access_erases (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h
  rw [consume_run]
  cases run : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk output t =>
    simp only [run] at hs hsafe hnormal erased
    cases output with
    | error e => exact ⟨suffix,hs,hsafe,True.intro⟩
    | ok out =>
      rcases out with ⟨value,v⟩
      have source : (liftWG (consumeDataDone pid pkt ep)).run w = .ok (value,v) := erased.symm
      have native : ((consumeDataDone pid pkt ep).run w.wg).run w.ambient =
          .ok ((value,v.wg),v.ambient) := by
        rw [liftWG_run] at source
        cases hr : ((consumeDataDone pid pkt ep).run w.wg).run w.ambient with
        | error e => simp only [hr,Except.map] at source; cases source
        | ok out =>
          rcases out with ⟨⟨x,g⟩,a⟩
          simp only [hr,Except.map,Except.ok.injEq,Prod.mk.injEq] at source
          rcases source with ⟨rfl,rfl⟩
          rfl
      let r : RxDisposition.ConsumeReceipt := ⟨pid,pkt,ep,⟨value,w.wg,v.wg,w.ambient,v.ambient⟩⟩
      have safe : Safe xs (t ++ [.consumed n skb stamp r]) := by
        intro q hq
        simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,receipt?,List.mem_append,List.mem_singleton] at hq
        rcases hq with old | rfl
        · exact hsafe q old
        · exact ⟨hi.2,native⟩
      cases value with
      | none => exact ⟨suffix ++ [.consumed n skb stamp r], by simp [hs,List.append_assoc,r],safe,safe,hnormal.2⟩
      | some bytes =>
        let entry : RxJoint.Entry := ⟨⟨n,skb,bytes⟩,stamp,some r⟩
        have safe' : Safe xs (t ++ [.consumed n skb stamp r] ++ [.buffered entry]) := by
          simpa only [Safe,List.filterMap_append,List.filterMap_cons,receipt?,List.filterMap_nil,List.append_nil] using safe
        exact ⟨suffix ++ [.consumed n skb stamp r] ++ [.buffered entry],
          by simp [hs,List.append_assoc,r,entry],safe',safe',hnormal.2⟩

private theorem ambient (xs : FlatTable × FlatTable) (a : AmbientM α) :
    PrefixPreserves (Inv xs) (Safe xs) (liftPrefix (monadLift a : Leanux.M α)) :=
  lifted xs _ (ProjectedRetainsRoutingCall.of_same (fun initial =>
    productAmbient_spec a (fun w => routingView w.wg = initial) (fun _ _ h => h)))

private theorem enter_routing (xs : FlatTable × FlatTable) (e : RxJoint.Entry) :
    PrefixPreserves (Inv xs) (Safe xs) (enter e) := by
  unfold enter
  exact (emit_quiet xs _ rfl).bind (fun _ =>
    receipt_quiet xs _ (access_routing xs _ (stackReceivePrefix_erases _) (deliverInner_routing _))
      _ (fun _ => rfl))

private theorem flush_routing (xs : FlatTable × FlatTable) (entries : List RxJoint.Entry) :
    PrefixPreserves (Inv xs) (Safe xs) (flush entries) :=
  PrefixPreserves.forM _ _ (fun _ _ hi => hi.1) (enter_routing xs)

private theorem normalList_routing (xs : FlatTable × FlatTable) (g : Gro) :
    PrefixPreserves (Inv xs) (Safe xs) (normalList g) := by
  unfold normalList
  split
  · exact PrefixPreserves.pure (fun _ _ hi => hi.1) _
  · exact (flush_routing xs _).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.1) _)

private theorem normalOne_routing (xs : FlatTable × FlatTable) (g : Gro) (e : RxJoint.Entry) (n : Nat) :
    PrefixPreserves (Inv xs) (Safe xs) (normalOne g e n) := by
  unfold normalOne
  dsimp only
  split
  · exact normalList_routing xs _
  · exact PrefixPreserves.pure (fun _ _ hi => hi.1) _

/-- GRO invokes the actual stack observer. A callback may delete peers; its
routing retention keeps the same flat tables for every subsequent consume. -/
theorem receive_routing (xs : FlatTable × FlatTable) (g : Gro) (e : RxJoint.Entry) :
    PrefixPreserves (Inv xs) (Safe xs) (receive g e) := by
  have safe : ∀ h w, Inv xs h w → Safe xs h := fun _ _ hi => hi.1
  have stopped {α : Type} (message : String) :
      PrefixPreserves (Inv xs) (Safe xs) (liftPrefix (unsupported message : Leanux.M α)) := by
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ safe
    intro h w x v hi hr
    change (Except.error _ : Except Stop _) = _ at hr
    cases hr
  unfold receive
  repeat' first
    | with_reducible exact normalOne_routing xs _ _ _
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible exact stopped _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

private theorem flushAll_routing (xs : FlatTable × FlatTable) (g : Gro) :
    PrefixPreserves (Inv xs) (Safe xs) (flushAll g) := by
  unfold flushAll
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.1)
    intro e g
    exact (normalOne_routing xs g e 1).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.1) _)
  · intro g
    exact (normalList_routing xs {g with held := []}).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.1) _)

private theorem capture_routing (xs : FlatTable × FlatTable) (skb : SkbId) :
    PrefixPreserves (Inv xs) (Safe xs) (capture skb) := by
  apply quiet xs _ (capture_appends skb)
  · intro w h
    rw [capture_run]
    cases (liftWG (getRxSkb skb)).run w <;> simp [receipt?,List.filterMap_append]
  · intro w h x v hi hr
    rw [capture_run] at hr
    cases hs : (liftWG (getRxSkb skb)).run w with
    | error e => simp [hs] at hr
    | ok out =>
      rcases out with ⟨p,u⟩
      simp only [hs,Except.ok.injEq,Prod.mk.injEq] at hr
      rcases hr with ⟨rfl,rfl⟩
      have frame : SameView routingView (getRxSkb skb) := by
        intro initial
        apply hoare_liftSkb
        intro g d store hg hd
        simpa only [routingView,hd,Option.map_some,routingState] using hg
      exact hi.retains ((ProjectedAction.iff_run _ _ _).mp
        (RetainsRoutingCall.liftWG (show RetainsRoutingCall _ from
          ProjectedRetainsRoutingCall.of_same frame)) w p u hs)

private theorem peek_routing (xs : FlatTable × FlatTable) (pid : PeerId) :
    PrefixPreserves (Inv xs) (Safe xs) (access (liftWGObserver (peekAccess pid))) := by
  apply native_access xs _ (peekAccess_erases pid)
  apply ProjectedRetainsRoutingCall.of_same
  have peek := fun (q : PrevQueue SkbId) => routing_kernel _ (prevQueuePeek_sameWGStore q)
  routing_handshake_source [peekRxQueue] using [peek]

private theorem ready_routing (xs : FlatTable × FlatTable) (first : Option SkbId) :
    PrefixPreserves (Inv xs) (Safe xs) (access (liftWGObserver (readyAccess first))) := by
  apply native_access xs _ (readyAccess_erases first)
  apply ProjectedRetainsRoutingCall.of_same
  have liftedAmbient {α : Type} (a : AmbientM α) : SameView routingView (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a _
  unfold WG.andM
  apply (liftedAmbient (AmbientM.branch .rxPollPacket first.isSome)).bind
  intro go
  split
  · cases first with
    | none => exact liftedAmbient (AmbientM.invariant _)
    | some skb =>
      apply (show SameView routingView (getRxSkb skb) from by
        intro initial
        apply hoare_liftSkb
        intro g d store hg hd
        simpa only [routingView,hd,Option.map_some,routingState] using hg).bind
      intro p
      exact liftedAmbient (AmbientM.branch .rxPollNotUncrypted (p.state != .uncrypted))
  · exact SameView.pure _ _

private theorem drop_routing (xs : FlatTable × FlatTable) (pid n skb : Nat) (stamp : PacketStamp) :
    PrefixPreserves (Inv xs) (Safe xs) (drop pid n skb stamp) := by
  unfold drop
  apply PrefixPreserves.bind
  · apply native_access xs _ (rxDropPeekedPrefix_erases pid)
    apply ProjectedRetainsRoutingCall.of_same
    rw [getPeer_twice]
    exact modifyPeer_routing pid _ (fun _ => rfl)
  · intro _
    exact emit_quiet xs _ rfl

private theorem complete_routing (xs : FlatTable × FlatTable) (pid : PeerId) :
    PrefixPreserves (Inv xs) (Safe xs) (access (liftWGObserver (completeAccess pid))) :=
  native_access xs _ (completeAccess_erases pid)
    (ProjectedRetainsRoutingCall.of_same (modifyPeer_routing pid _ (fun _ => rfl)))

private theorem option_routing (xs : FlatTable × FlatTable) (out : Option RxJoint.Entry) (g : Gro) :
    PrefixPreserves (Inv xs) (Safe xs)
      (forIn out.toList g (fun e g => do let g' ← receive g e; pure (.yield g'))) :=
  PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.1) (fun e g =>
    (receive_routing xs g e).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.1) _))

private theorem counter_routing (xs : FlatTable × FlatTable) (kp nonce : Nat) :
    PrefixPreserves (Inv xs) (Safe xs) (access (liftWGObserver (counterValidatePrefix kp nonce))) :=
  native_access xs _ (counterValidatePrefix_erases kp nonce)
    (ProjectedRetainsRoutingCall.of_same (counterValidate_routing kp nonce))

private theorem keyPut_routing (xs : FlatTable × FlatTable) (kp : Option KeypairId) (now : Bool) :
    PrefixPreserves (Inv xs) (Safe xs) (access (liftWGObserver (keypairPutPrefix kp now))) :=
  native_access xs _ (keypairPutPrefix_erases kp now)
    (ProjectedRetainsRoutingCall.of_same (keypairPut_routing kp now))

private theorem peerPut_routing (xs : FlatTable × FlatTable) (pid : Option PeerId) :
    PrefixPreserves (Inv xs) (Safe xs) (access (liftWGObserver (peerPutMixed pid))) :=
  native_access xs _ (peerPutMixed_erases pid) (peerPut_retainsRouting pid)

private theorem endpoint_routing (xs : FlatTable × FlatTable) (src : SkbSource) :
    PrefixPreserves (Inv xs) (Safe xs) (liftPrefix (liftWG (endpointFromSkb src))) :=
  lifted xs _ (RetainsRoutingCall.liftWG (ProjectedRetainsRoutingCall.of_same
    (routing_kernel _ (endpointFromSkb_sameWGStore src))))

macro "poll_routing_step " xs:term : tactic => `(tactic|
  repeat' first
    | rx_phase_reduce
    | (rx_phase_head plain Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.1) _)
    | (rx_phase_head plain capture; apply PrefixPreserves.bind (capture_routing $xs _))
    | (rx_phase_head plain drop; apply PrefixPreserves.bind (drop_routing $xs _ _ _ _))
    | (rx_phase_head plain consume; apply PrefixPreserves.bind (consume $xs _ _ _ _ _ _))
    | (rx_phase_head plain ForIn.forIn; apply PrefixPreserves.bind (option_routing $xs _ _))
    | (rx_phase_head plain flushAll; apply PrefixPreserves.bind (flushAll_routing $xs _))
    | (rx_phase_head plain peekAccess; apply PrefixPreserves.bind (peek_routing $xs _))
    | (rx_phase_head plain readyAccess; apply PrefixPreserves.bind (ready_routing $xs _))
    | (rx_phase_head plain completeAccess; apply PrefixPreserves.bind (complete_routing $xs _))
    | (rx_phase_head receipt counterValidatePrefix; apply PrefixPreserves.bind
        (receipt_quiet $xs _ (counter_routing $xs _ _) _ (fun _ => rfl)))
    | (rx_phase_head receipt branch; apply PrefixPreserves.bind
        (receipt_quiet $xs _ (ambient $xs (AmbientM.branch _ _)) _ (fun _ => rfl)))
    | (rx_phase_head receipt endpointFromSkb; apply PrefixPreserves.bind
        (receipt_quiet $xs _ (endpoint_routing $xs _) _ (fun _ => rfl)))
    | (rx_phase_head plain keypairPutPrefix; apply PrefixPreserves.bind (keyPut_routing $xs _ _))
    | (rx_phase_head plain peerPutMixed; apply PrefixPreserves.bind (peerPut_routing $xs _))
    | (rx_phase_head plain freeRxSkbPrefix; apply PrefixPreserves.bind
        (native_access $xs _ (freeRxSkbPrefix_erases _) (ProjectedRetainsRoutingCall.of_same (by
          intro initial
          apply hoare_liftSkb
          intro g d store hg hd
          simpa only [id,routingView,hd,Option.map_some,routingState] using hg))))
    | (rx_phase_head plain branch; apply PrefixPreserves.bind (ambient $xs (AmbientM.branch _ _)))
    | (rx_phase_head plain invariant; apply PrefixPreserves.bind (ambient $xs (AmbientM.invariant _)))
    | (rx_phase_head plain unsupported; apply PrefixPreserves.bind (ambient $xs (AmbientM.unsupported _)))
    | (rx_phase_head plain ite; apply PrefixPreserves.ite)
    | rx_phase_intro
    | rx_phase_match)

/-- Every captured consume has this poll's entry flat routing tables at its
actual before state. Earlier receipts require their own certificate; failed
polls retain all certificates emitted before the Stop. -/
theorem poll (xs : FlatTable × FlatTable) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Inv xs) (Safe xs) (RxJoint.poll pid budget) := by
  unfold RxJoint.poll
  apply PrefixPreserves.bind (ambient xs (AmbientM.branch _ _))
  intro noBudget
  split
  · exact PrefixPreserves.pure (fun _ _ hi => hi.1) _
  · apply PrefixPreserves.bind
    · apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.1)
      intro index acc
      poll_routing_step xs
    · intro acc
      poll_routing_step xs

/-- With a checked incoming local history, every emitted consume is certified
at its own entry cut, even when a later poll action Stops. -/
theorem consumed (xs : FlatTable × FlatTable) (pid : PeerId) (budget : Nat)
    (w : World) (h : List Event) (hi : RoutedView (routingView w.wg) xs)
    (history : Safe xs h) (n skb : Nat) (stamp : PacketStamp) (r : RxDisposition.ConsumeReceipt)
    (member : Event.consumed n skb stamp r ∈ (runPrefix (RxJoint.poll pid budget) w h).2) :
    RoutedView (routingView r.run.before) xs ∧ r.Valid := by
  obtain ⟨_,_,safe,_⟩ := poll xs pid budget w h ⟨history,hi⟩
  exact safe r (List.mem_filterMap.mpr ⟨_,member,rfl⟩)

private theorem seed_safe (xs : FlatTable × FlatTable) (prior : List LifetimeEvent) :
    Safe xs (seed prior) := by
  have noReceipts : (seed prior).filterMap receipt? = [] :=
    filterMap_disjoint Event.access receipt? (fun _ => rfl) prior
  intro r hr
  rw [noReceipts] at hr
  cases hr

/-- The global observer accepts every incoming history. Only its newly
produced suffix is certified; no claim is made about arbitrary prior receipts.
Normal endpoints retain the same flat tables, and Stops retain the reached
consume certificates in their exact observed order. -/
theorem observePoll (xs : FlatTable × FlatTable) (pid : PeerId) (budget : Nat)
    (w : World) (h : List RxHistory.Event) (hi : RoutedView (routingView w.wg) xs) :
    ∃ suffix : List Event,
      (runPrefix (RxHistory.observePoll pid budget) w h).2 = h ++ suffix.map RxHistory.promote ∧
      Safe xs suffix ∧
      match (runPrefix (RxHistory.observePoll pid budget) w h).1 with
      | .error _ => True
      | .ok (_,v) => RoutedView (routingView v.wg) xs := by
  obtain ⟨suffix,hs,safe,normal⟩ := poll xs pid budget w (seed (RxHistory.prior h))
    ⟨seed_safe xs _,hi⟩
  have actual := RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl hs)
  refine ⟨suffix,congrArg Prod.snd actual,?_,?_⟩
  · intro r hr
    apply safe r
    rw [hs,List.filterMap_append]
    exact List.mem_append_right _ hr
  · rw [congrArg Prod.fst actual]
    cases result : (runPrefix (RxJoint.poll pid budget) w (seed (RxHistory.prior h))).1 with
    | error e => trivial
    | ok out =>
      simp only [result] at normal
      exact normal.2

end Leanux.Proofs.WG.Queues.PollRouting
