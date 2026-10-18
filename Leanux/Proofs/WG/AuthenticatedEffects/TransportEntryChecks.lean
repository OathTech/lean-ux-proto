import Leanux.Proofs.WG.Packets.PublicationStack
import Leanux.Proofs.WG.Packets.PublicationConsumeHistory

/-! Packet publication anchors at the actual replay-check entry, before any
consume or endpoint effect. These existing journal events survive an internally
stopped consume. The enclosing caller must supply the same publication history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportEntryChecks
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues RxJoint

def counterEntry : RxJoint.Event → Option (RxPacket × RunWitness Bool)
  | .checkedCounter _ _ _ pkt r => some (pkt,r)
  | _ => none

def Checks (history : List RxHistory.Event) (h : List RxJoint.Event) : Prop :=
  ∀ r ∈ h.filterMap counterEntry,
    PublicationHistory.Inv history r.2.before.wg ∧ r.1.state = .crypted

def State (history : List RxHistory.Event) (h : List RxJoint.Event) (w : World) : Prop :=
  PublicationHistory.Inv history w.wg ∧ Checks history h

private theorem checks_append (a b : List RxJoint.Event) :
    Checks history (a ++ b) ↔ Checks history a ∧ Checks history b := by
  constructor
  · intro hi
    exact ⟨fun r hr => hi r (by simpa only [List.filterMap_append,List.mem_append] using Or.inl hr),
      fun r hr => hi r (by simpa only [List.filterMap_append,List.mem_append] using Or.inr hr)⟩
  · rintro ⟨ha,hb⟩ r hr
    rw [List.filterMap_append,List.mem_append] at hr
    exact hr.elim (ha r) (hb r)

private theorem checks_emit (h : List RxJoint.Event) (e : RxJoint.Event)
    (hi : Checks history h)
    (he : ∀ r, counterEntry e = some r →
      PublicationHistory.Inv history r.2.before.wg ∧ r.1.state = .crypted) :
    Checks history (h ++ [e]) := by
  apply (checks_append h [e]).mpr
  refine ⟨hi,?_⟩
  intro r hr
  obtain ⟨x,hx,hr⟩ := List.mem_filterMap.mp hr
  simp only [List.mem_singleton] at hx
  subst x
  exact he r hr

private theorem quiet (g : Obs α) (a : Leanux.M α) (history : List RxHistory.Event)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (frame : HistoryFrame counterEntry g)
    (preserves : Preserves (fun w : World => PublicationHistory.Inv history w.wg) a) :
    PrefixPreserves (State history) (Checks history) g := by
  intro w h hi
  obtain ⟨s,hs⟩ := appends w h
  have safe : Checks history (runPrefix g w h).2 := by
    unfold Checks
    rw [frame w h]
    exact hi.2
  refine ⟨s,hs,safe,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    exact ⟨(hoare_iff_run _ _ _).mp preserves w out.1 out.2 hi.1
      ((erases w h).symm.trans hr),safe⟩

/-- The access observer remains arbitrary in the actual product monad. -/
private theorem access_rule (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (history : List RxHistory.Event) (erases : ErasesPrefix g a)
    (preserves : Preserves (fun w : World => PublicationHistory.Inv history w.wg) a) :
    PrefixPreserves (State history) (Checks history) (access g) :=
  quiet _ a history (access_appends g) (access_erases erases)
    (fun w h => focusPrefix_other Event.access accessEvent counterEntry (fun _ => rfl) g w h)
    preserves

private theorem native_access (g : MixedM α) (a : WG.M α)
    (history : List RxHistory.Event) (erases : ErasesStatePrefix g a)
    (preserves : Preserves (PublicationHistory.Inv history) a) :
    PrefixPreserves (State history) (Checks history) (access (liftWGObserver g)) :=
  access_rule _ _ history (liftWGObserver_erases erases)
    (PublicationPoll.native_product _ a preserves)

private theorem lift_rule (a : Leanux.M α) (history : List RxHistory.Event)
    (preserves : Preserves (fun w : World => PublicationHistory.Inv history w.wg) a) :
    PrefixPreserves (State history) (Checks history) (liftPrefix a) :=
  quiet _ a history (Appends.lift a) (erasesPrefix_lift a) (HistoryFrame.lift _ a) preserves

private theorem emit_rule (e : RxJoint.Event) (history : List RxHistory.Event)
    (he : counterEntry e = none) :
    PrefixPreserves (State history) (Checks history) (emitPrefix e) := by
  intro w h hi
  have safe := checks_emit h e hi.2 (by intro r hr; rw [he] at hr; cases hr)
  exact ⟨[e],rfl,safe,hi.1,safe⟩

private theorem receipt_rule (a : Obs α) (event : RunWitness α → RxJoint.Event)
    (history : List RxHistory.Event)
    (ha : PrefixPreserves (State history) (Checks history) a)
    (he : ∀ r, counterEntry (event r) = none) :
    PrefixPreserves (State history) (Checks history) (receiptObserved a event) := by
  unfold receiptObserved
  exact ha.captureObserved.bind (fun r => (emit_rule _ history (he r)).bind
    (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _))

private theorem capture_rule (id : SkbId) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (capture id) := by
  intro w h hi
  rw [capture_run]
  cases hr : (liftWG (getRxSkb id)).run w with
  | error e => exact ⟨[],by simp,hi.2,True.intro⟩
  | ok out =>
    rcases out with ⟨pkt,v⟩
    have frame := (hoare_iff_run _ _ _).mp
      (PublicationPoll.native_product _ _
        ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationPoll.«0».Leanux.Proofs.WG.PublicationPoll.readRx_preserves) id history))
      w pkt v hi.1 hr
    have safe := checks_emit h (.access (.packet (.read (.inr id) (packetStamp w.wg id)))) hi.2
      (by intro r impossible; cases impossible)
    exact ⟨[_],rfl,safe,frame,safe⟩

private theorem drop_rule (pid n id : Nat) (stamp : PacketStamp) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (drop pid n id stamp) := by
  unfold drop
  exact (native_access _ _ history (rxDropPeekedPrefix_erases pid)
    (PublicationPoll.drop_preserves pid history)).bind (fun _ => emit_rule _ history rfl)

private theorem consume_rule (pid n id : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (ep : Endpoint) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (consume pid n id stamp pkt ep) := by
  intro w h hi
  obtain ⟨s,hs,safe,normal⟩ := native_access _ _ history
    (consumeDataDonePrefix_erases pid pkt ep)
    (PublicationCompletion.consumeDataDone_preserves pid pkt ep history) w h hi
  rw [consume_run]
  cases hr : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t =>
    simp only [hr] at hs safe normal
    cases result with
    | error e => exact ⟨s,hs,safe,True.intro⟩
    | ok out =>
      rcases out with ⟨returned,v⟩
      let receipt : RxDisposition.ConsumeReceipt := ⟨pid,pkt,ep,⟨returned,w.wg,v.wg,w.ambient,v.ambient⟩⟩
      have cut : Checks history (t ++ [.consumed n id stamp receipt]) :=
        checks_emit _ _ safe (by intro r hr; cases hr)
      cases returned with
      | none =>
        exact ⟨s ++ [.consumed n id stamp receipt],by simp only [hs,List.append_assoc]; rfl,cut,normal.1,cut⟩
      | some bytes =>
        let entry : Entry := ⟨⟨n,id,bytes⟩,stamp,some receipt⟩
        have buffered := checks_emit (t ++ [.consumed n id stamp receipt]) (.buffered entry) cut
          (by intro r impossible; cases impossible)
        exact ⟨s ++ [_,_],by simp only [hs,List.append_assoc]; rfl,buffered,normal.1,buffered⟩

private theorem state_bind (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (history : List RxHistory.Event) (f : Bool → Obs α)
    (hf : ∀ b, b = (pkt.state != .crypted) →
      PrefixPreserves (State history) (Checks history) (f b)) :
    PrefixPreserves (State history) (Checks history)
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState n id stamp pkt) >>= f) := by
  have step : PrefixEnsures (State history) (Checks history)
      (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
      (fun b h w => State history h w ∧ b = (pkt.state != .crypted)) := by
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.2)
    intro w h b v hi hr
    cases hr
    exact ⟨hi,rfl⟩
  unfold receiptObserved
  simp only [bind_assoc,pure_bind]
  apply PrefixEnsures.bind step.captureObserved
  intro r
  apply PrefixEnsures.bind (Q := fun _ h w => State history h w ∧ r.value = (pkt.state != .crypted))
  · intro w h hi
    obtain ⟨s,hs,safe,normal⟩ := emit_rule (Event.checkedState n id stamp pkt r) history rfl w h (hi.1 ▸ hi.2.1.1)
    exact ⟨s,hs,safe,normal,hi.2.1.2⟩
  · intro _
    intro w h hi
    exact hf r.value hi.2 w h hi.1

private theorem enter_rule (e : Entry) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (enter e) := by
  unfold enter
  apply PrefixPreserves.bind (emit_rule _ history rfl)
  intro _
  exact receipt_rule _ _ history
    (access_rule _ _ history (stackReceivePrefix_erases e.tag.bytes)
      (PublicationStack.deliverInner_preserves e.tag.bytes history)) (fun _ => rfl)

private theorem flush_rule (es : List Entry) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (flush es) :=
  PrefixPreserves.forM es enter (fun _ _ hi => hi.2) (fun e => enter_rule e history)

private theorem normalList_rule (g : Gro) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (normalList g) := by
  unfold normalList
  split
  · exact PrefixPreserves.pure (fun _ _ hi => hi.2) _
  · exact (flush_rule _ history).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _)

private theorem normalOne_rule (g : Gro) (e : Entry) (n : Nat) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (normalOne g e n) := by
  unfold normalOne
  dsimp only
  split
  · exact normalList_rule _ history
  · exact PrefixPreserves.pure (fun _ _ hi => hi.2) _

private theorem receive_rule (g : Gro) (e : Entry) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (receive g e) := by
  have safe : ∀ h w, State history h w → Checks history h := fun _ _ hi => hi.2
  have stopped {α : Type} (message : String) :
      PrefixPreserves (State history) (Checks history) (liftPrefix (unsupported message : Leanux.M α)) := by
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ safe
    intro h w x v hi hr
    change (Except.error _ : Except Stop _) = _ at hr
    cases hr
  unfold receive
  repeat' first
    | exact normalOne_rule _ _ _ history
    | exact stopped _
    | exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

private theorem flushAll_rule (g : Gro) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (flushAll g) := by
  unfold flushAll
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn
    · exact fun _ _ hi => hi.2
    · intro e g
      exact (normalOne_rule g e 1 history).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  · intro g
    exact (normalList_rule {g with held := []} history).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _)

private theorem ready_rule (first : Option SkbId) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (access (liftWGObserver (readyAccess first))) := by
  apply native_access _ _ history (readyAccess_erases first)
  unfold WG.andM branch invariant
  repeat' publication_poll_native history

private theorem endpoint_rule (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history)
      (receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
        (Event.checkedEndpoint n id stamp pkt)) :=
  receipt_rule _ _ history
    (lift_rule _ history (PublicationPoll.native_product _ _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationPoll.«0».Leanux.Proofs.WG.PublicationPoll.store)
        _ (endpointFromSkb_sameWGStore _) history))) (fun _ => rfl)

private theorem counter_rule (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (history : List RxHistory.Event) (crypted : pkt.state = .crypted) :
    PrefixPreserves (State history) (Checks history)
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (Event.checkedCounter n id stamp pkt)) := by
  unfold receiptObserved
  apply PrefixEnsures.bind (PrefixEnsures.captureObserved (native_access _ _ history
    (counterValidatePrefix_erases _ _) (PublicationPoll.counterValidate_preserves _ _ history)))
  intro r w h hi
  have current : State history h w := hi.1 ▸ hi.2.1
  obtain ⟨before,prior,_⟩ := hi.2.2
  have checked := checks_emit h (Event.checkedCounter n id stamp pkt r) current.2
    (by intro entry eq; cases eq; exact ⟨prior.1,crypted⟩)
  exact ⟨[_],rfl,checked,current.1,checked⟩

private theorem keep_bind (g : Obs α) (f : α → Obs β) (history : List RxHistory.Event)
    (hg : PrefixPreserves (State history) (Checks history) g)
    (hf : ∀ x, PrefixPreserves (State history) (Checks history) (f x)) :
    PrefixPreserves (State history) (Checks history) (g >>= f) := hg.bind hf

private theorem crypted_of_test (s : PacketState) (hs : (s != .crypted) = false) : s = .crypted := by
  cases s <;> first | rfl | cases hs

macro "transport_entry_checks_step " history:term : tactic => `(tactic| first
  | rx_phase_reduce
  | (rx_phase_head plain Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (rx_phase_head plain capture; apply keep_bind _ _ $history (capture_rule _ $history))
  | (rx_phase_head plain drop; apply keep_bind _ _ $history (drop_rule _ _ _ _ $history))
  | (rx_phase_head plain consume; apply keep_bind _ _ $history (consume_rule _ _ _ _ _ _ $history))
  | (rx_phase_head plain receive; apply keep_bind _ _ $history (receive_rule _ _ $history))
  | (rx_phase_head plain flushAll; apply keep_bind _ _ $history (flushAll_rule _ $history))
  | (rx_phase_head plain peekAccess; apply keep_bind _ _ $history (native_access _ _ $history
      (peekAccess_erases _) (PublicationPoll.peek_preserves _ $history)))
  | (rx_phase_head plain readyAccess; apply keep_bind _ _ $history (ready_rule _ $history))
  | (rx_phase_head plain completeAccess; apply keep_bind _ _ $history (native_access _ _ $history
      (completeAccess_erases _) (PublicationPoll.complete_preserves _ $history)))
  | (rx_phase_head receipt branch; apply state_bind _ _ _ _ $history)
  | (rx_phase_head receipt counterValidatePrefix; apply keep_bind _ _ $history (counter_rule _ _ _ _ $history
      (by apply crypted_of_test; simp_all)))
  | (rx_phase_head receipt endpointFromSkb; apply keep_bind _ _ $history (endpoint_rule _ _ _ _ $history))
  | (rx_phase_head plain keypairPutPrefix; apply keep_bind _ _ $history (native_access _ _ $history
      (keypairPutPrefix_erases _ _) (PublicationPoll.keypairPut_preserves _ _ $history)))
  | (rx_phase_head plain peerPutMixed; apply keep_bind _ _ $history (native_access _ _ $history
      (peerPutMixed_erases _) (PublicationPoll.peerPut_preserves _ $history)))
  | (rx_phase_head plain freeRxSkbPrefix; apply keep_bind _ _ $history (native_access _ _ $history
      (freeRxSkbPrefix_erases _) (PublicationHistory.freeRxSkb_preserves _ $history)))
  | (rx_phase_head plain branch; apply keep_bind _ _ $history (lift_rule _ $history
      (productAmbient_spec (AmbientM.branch _ _) _ (fun _ _ hi => hi))))
  | (rx_phase_head plain invariant; apply keep_bind _ _ $history (lift_rule _ $history
      (productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi))))
  | (rx_phase_head plain unsupported; apply keep_bind _ _ $history (lift_rule _ $history
      (productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ hi => hi))))
  | (rx_phase_head plain ite; apply PrefixPreserves.ite)
  | rx_phase_intro
  | rx_phase_match)

/-- Every original replay-check receipt has a publication invariant at its
actual input and passed the crypted-state guard, even before a later Stop. -/
theorem poll (pid : PeerId) (budget : Nat) (history : List RxHistory.Event) :
    PrefixPreserves (State history) (Checks history) (RxJoint.poll pid budget) := by
  unfold RxJoint.poll
  repeat' first
    | exact fun _ _ hi => hi.2
    | transport_entry_checks_step history
    | (rx_phase_head plain ForIn.forIn
       apply keep_bind _ _ history
       first | apply PrefixPreserves.range | apply PrefixPreserves.forIn)
    | exact And.right ‹State history _ _›

/-- The fresh nested journal carries only lifetime accesses before this poll;
its safety conclusion includes every receipt emitted before a later Stop. -/
theorem poll_seed (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent)
    (history : List RxHistory.Event) (hi : PublicationHistory.Inv history w.wg) :
    Checks history (runPrefix (RxJoint.poll pid budget) w (seed prior)).2 := by
  apply (poll pid budget history w (seed prior) _).choose_spec.2.1
  refine ⟨hi,?_⟩
  intro r hr
  have empty : (seed prior).filterMap counterEntry = [] :=
    filterMap_disjoint Event.access counterEntry (fun _ => rfl) prior
  rw [empty] at hr
  cases hr

/-- The original native replay call and input-state facts refer to the same
existing receipt. This is a poll-entry result; selected-cell linkage and the
initialized whole-run transport are deliberately not hypotheses in disguise. -/
theorem poll_counter_entry (pid : PeerId) (budget : Nat) (w : World)
    (prior : List LifetimeEvent) (history : List RxHistory.Event)
    (hi : PublicationHistory.Inv history w.wg)
    (occurrence id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (r : RunWitness Bool)
    (member : Event.checkedCounter occurrence id stamp pkt r ∈
      (runPrefix (RxJoint.poll pid budget) w (seed prior)).2) :
    PublicationHistory.Inv history r.before.wg ∧ pkt.state = .crypted ∧
      r.Valid (liftWG (counterValidate pkt.keypair pkt.nonce)) := by
  have checked := poll_seed pid budget w prior history hi (pkt,r)
    (List.mem_filterMap.mpr ⟨_,member,rfl⟩)
  exact ⟨checked.1,checked.2,
    RxDisposition.poll_seed_valid pid budget w prior _ member⟩

/-- The persistent receive observer promotes these same pre-consume receipts,
including those retained when the consumer later stops internally. -/
theorem observePoll_counter_entry (pid : PeerId) (budget : Nat) (w : World)
    (history : List RxHistory.Event) (hi : PublicationHistory.Inv history w.wg) :
    ∃ suffix : List RxJoint.Event,
      runPrefix (RxHistory.observePoll pid budget) w history =
        ((runPrefix (RxJoint.poll pid budget) w (seed (RxHistory.prior history))).1,
          history ++ suffix.map RxHistory.promote) ∧
      ∀ occurrence id stamp pkt r, Event.checkedCounter occurrence id stamp pkt r ∈ suffix →
        PublicationHistory.Inv history r.before.wg ∧ pkt.state = .crypted ∧
          r.Valid (liftWG (counterValidate pkt.keypair pkt.nonce)) := by
  obtain ⟨suffix,hs⟩ := RxJoint.poll_appends pid budget w (seed (RxHistory.prior history))
  refine ⟨suffix,RxHistory.observePoll_suffix pid budget w history _ suffix (Prod.ext rfl hs),?_⟩
  intro occurrence id stamp pkt r member
  apply poll_counter_entry pid budget w (RxHistory.prior history) history hi occurrence id stamp pkt r
  rw [hs]
  exact List.mem_append_right _ member

end Leanux.Proofs.WG.AuthenticatedEffects.TransportEntryChecks
