import Leanux.Proofs.WG.Queues.RxConsumeLink

/-! Source-specific selection phases for the unchanged joint poll. The live
cell relation ends at consume entry; GRO and later callbacks retain only its
immutable receipt and ordered journal support. -/
namespace Leanux.Proofs.WG.Queues.RxLink
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes RxJoint RxDisposition

/-- Retain a live selected cell only across an original operation with the
actual full-store frame. Historical support is transported by its real suffix. -/
theorem phase_keep {F : List RxJoint.Event → Prop} (a : Obs α) (original : M α)
    (ha : PrefixPreserves (Context base g) (Linked base) a)
    (he : ErasesPrefix a original) (hf : SameView rxStore original)
    (hm : ∀ h t, F h → F (h ++ t)) :
    PrefixPreserves (fun h w => Context base g h w ∧ SelectedAt skb stamp pkt w ∧ F h)
      (Linked base) a := by
  intro w h hi
  obtain ⟨s,hs,hl,hn⟩ := ha w h hi.1
  refine ⟨s,hs,hl,?_⟩
  cases hr : (runPrefix a w h).1 with
  | error e => trivial
  | ok out =>
    exact ⟨by simpa only [hr] using hn,
      selected_transport skb stamp pkt w out.2 (hf w out.1 out.2 ((he w h).symm.trans hr)) hi.2.1,
      hs ▸ hm h s hi.2.2⟩

theorem receipt_erases (ha : ErasesPrefix a original) : ErasesPrefix (receiptObserved a f) original := by
  intro w h
  rw [runPrefix_receiptObserved]
  cases hr : runPrefix a w h with
  | mk out t => cases out <;> simpa only [hr] using ha w h

theorem capture_link (skb : SkbId) :
    PrefixEnsures (Context base g) (Linked base) (capture skb)
      (fun out h w => Context base g h w ∧ SelectedAt skb out.2 out.1 w ∧ ReadSince base h skb out.2) := by
  intro w h hi
  rw [capture_run]
  cases hr : (getRxSkb skb).run w with
  | error e => exact ⟨[],by simp,hi.1,True.intro⟩
  | ok out =>
    rcases out with ⟨pkt,v⟩
    obtain ⟨hv,d,hd,hp⟩ := Packets.getRxSkb_current skb w v pkt hr
    subst v
    let ev := readEvent skb (packetStamp w skb)
    have hl := hi.1.snoc (e := ev) True.intro
    obtain ⟨s,hs⟩ := hi.1.extension
    refine ⟨[ev],rfl,hl,⟨hl,hi.2.append [ev]⟩,?_,?_⟩
    · exact ⟨rfl,by simp [rxStore,hd,hp]⟩
    · exact ⟨s,[],by simp only [hs,List.append_nil]; rfl⟩

abbrev Picked (base : List RxJoint.Event) (g : Gro) (n skb : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (h : List RxJoint.Event) (w : World) : Prop :=
  Context base g h w ∧ SelectedAt skb stamp pkt w ∧ ReadBeforeRemoval base h (n,skb,stamp)

theorem drop_link (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixEnsures (fun h w => Context base g h w ∧ SelectedAt skb stamp pkt w ∧ ReadSince base h skb stamp)
      (Linked base) (drop pid n skb stamp) (fun _ => Picked base g n skb stamp pkt) := by
  unfold drop
  apply PrefixEnsures.bind (Q := fun _ h w => Context base g h w ∧ SelectedAt skb stamp pkt w ∧ ReadSince base h skb stamp)
    (show PrefixEnsures _ _ (access (rxDropPeekedPrefix pid))
      (fun _ h w => Context base g h w ∧ SelectedAt skb stamp pkt w ∧ ReadSince base h skb stamp) from
      phase_keep (base := base) (g := g) (skb := skb) (stamp := stamp) (pkt := pkt)
        (F := fun h => ReadSince base h skb stamp) _ _ (keep _ (linked_access _))
        (access_erases (rxDropPeekedPrefix_erases pid)) (drop_rxStore pid)
        (fun _ t hi => hi.append t))
  intro _ w h hi
  have hl := hi.1.1.snoc (e := .removed n skb stamp) True.intro
  obtain ⟨a,b,hab⟩ := hi.2.2
  refine ⟨[.removed n skb stamp],rfl,hl,⟨hl,hi.1.2.append _⟩,hi.2.1,?_⟩
  exact ⟨a,b,[],by simp only [runPrefix_emit,hab,List.append_nil,readEvent]⟩

theorem picked_lift (a : M α) (ha : SameKernel a) :
    PrefixPreserves (Picked base g n skb stamp pkt) (Linked base) (liftPrefix a) :=
  phase_keep _ _ (keep _ (linked_lift _)) (erasesPrefix_lift _)
    (by intro w x v hr; unfold rxStore; rw [ha w x v hr]) (fun _ t hi => hi.append t)

theorem picked_receipt_lift (a : M α) (ha : SameKernel a) (f : RunWitness α → RxJoint.Event)
    (hf : ∀ h r, EventLink base h (f r)) :
    PrefixPreserves (Picked base g n skb stamp pkt) (Linked base) (receiptObserved (liftPrefix a) f) :=
  phase_keep _ _ (keep _ (linked_receipt _ _ (linked_lift _) hf))
    (receipt_erases (erasesPrefix_lift _)) (by intro w x v hr; unfold rxStore; rw [ha w x v hr]) (fun _ t hi => hi.append t)

theorem picked_counter (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Picked base g n skb stamp pkt) (Linked base)
      (receiptObserved (access (counterValidatePrefix pkt.keypair pkt.nonce))
        (RxJoint.Event.checkedCounter n skb stamp pkt)) :=
  phase_keep _ _ (keep _ (linked_receipt _ _ (linked_access _) (fun _ _ => True.intro)))
    (receipt_erases (access_erases (counterValidatePrefix_erases _ _)))
    (counter_rxStore _ _) (fun _ t hi => hi.append t)

theorem picked_state (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Picked base g n skb stamp pkt) (Linked base)
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (RxJoint.Event.checkedState n skb stamp pkt)) :=
  picked_receipt_lift _ (sameKernel_branch _ _) _ (fun _ _ => True.intro)

theorem picked_endpoint (n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Picked base g n skb stamp pkt) (Linked base)
      (receiptObserved (liftPrefix (endpointFromSkb pkt.source))
        (RxJoint.Event.checkedEndpoint n skb stamp pkt)) :=
  picked_receipt_lift _ (endpointFromSkb_sameKernel _) _ (fun _ _ => True.intro)

theorem consume_context (g : Gro) (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint)
    (hp : pkt.peer = pid) :
    PrefixEnsures (Picked base g n skb stamp pkt) (Linked base)
      (consume pid n skb stamp pkt ep)
      (fun out h w => Context base g h w ∧ Supported base h out.toList) := by
  have hc := remember (consume_link (base := base) pid n skb stamp pkt ep)
    (F := fun h => Supported base h (g.rxList ++ g.held)) (fun _ t hi => hi.append t)
  exact hc.consequence
    (fun h w hi => ⟨⟨hi.1.1,hi.2.1,hp,hi.2.2⟩,hi.1.2⟩)
    (fun _ _ _ hi => ⟨⟨hi.1.1,hi.2⟩,hi.1.2⟩)

theorem option_context (g : Gro) (out : Option Entry) :
    PrefixEnsures (fun h w => Context base g h w ∧ Supported base h out.toList) (Linked base)
      (forIn out.toList g (fun e cur => do let cur' ← receive cur e; pure (.yield cur'))) (Context base) := by
  cases out with
  | none => exact PrefixEnsures.pure (fun _ _ hi => hi.1.1) (fun _ _ hi => hi.1)
  | some e =>
    simpa only [Option.toList_some,List.forIn_cons,List.forIn_nil,bind_assoc,pure_bind,bind_pure] using
      (receive_link (base := base) g e).consequence
        (fun _ _ hi => ⟨hi.1,hi.2 e (by simp)⟩) (fun _ _ _ hi => hi)

theorem keep_bind (a : Obs α) (f : α → Obs β)
    (ha : PrefixPreserves I (Linked base) a)
    (hf : ∀ x, PrefixEnsures I (Linked base) (f x) Q) :
    PrefixEnsures I (Linked base) (a >>= f) Q :=
  PrefixEnsures.bind (Q := fun _ => I) ha hf

theorem stop_bind (a : M Unit) (ha : ∀ w, ∃ e, a.run w = .error e)
    (hs : ∀ h w, P h w → Linked base h) (f : Unit → Obs α) :
    PrefixEnsures P (Linked base) (liftPrefix a >>= f) Q := by
  intro w h hi
  obtain ⟨e,he⟩ := ha w
  simp only [runPrefix_bind,runPrefix_lift,he]
  exact ⟨[],by simp,hs h w hi,True.intro⟩

theorem stop_context (a : M Unit) (ha : ∀ w, ∃ e, a.run w = .error e) (f : Unit → Obs α) :
    PrefixEnsures (Context base g) (Linked base) (liftPrefix a >>= f) Q :=
  stop_bind a ha (fun _ _ hi => hi.1) f

theorem stop_selected {R : List RxJoint.Event → World → Prop}
    (a : M Unit) (ha : ∀ w, ∃ e, a.run w = .error e) (f : Unit → Obs α) :
    PrefixEnsures (fun h w => Context base g h w ∧ R h w) (Linked base) (liftPrefix a >>= f) Q :=
  stop_bind a ha (fun _ _ hi => hi.1.1) f

theorem cleanup_link (kp : Option KeypairId) (now : Bool) (f : Unit → Obs α)
    (hf : PrefixEnsures (Context base g) (Linked base) (access (keypairPutPrefix kp now) >>= f) Q) :
    PrefixEnsures (Picked base g n skb stamp pkt) (Linked base)
      (access (keypairPutPrefix kp now) >>= f) Q :=
  hf.consequence (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

macro "rx_link_step" : tactic => `(tactic|
  repeat' first
    | exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
    | exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi.1)
    | exact PrefixEnsures.pure (fun _ _ hi => hi.1.1) (fun _ _ hi => hi.1)
    | with_reducible apply stop_context (invariant _) (fun _ => ⟨_,rfl⟩)
    | with_reducible apply stop_selected (invariant _) (fun _ => ⟨_,rfl⟩)
    | with_reducible apply stop_context (unsupported _) (fun _ => ⟨_,rfl⟩)
    | with_reducible apply PrefixEnsures.bind (capture_link _)
    | with_reducible apply PrefixEnsures.bind (drop_link _ _ _ _ _)
    | (with_reducible apply PrefixEnsures.bind (consume_context _ _ _ _ _ _ _ (by simp_all)))
    | with_reducible apply PrefixEnsures.bind (option_context _ _)
    | with_reducible apply PrefixEnsures.bind (flushAll_link _)
    | with_reducible apply keep_bind _ _ (picked_counter _ _ _ _)
    | with_reducible apply keep_bind _ _ (picked_state _ _ _ _)
    | with_reducible apply keep_bind _ _ (picked_endpoint _ _ _ _)
    | with_reducible apply keep_bind _ _ (picked_lift _ (sameKernel_branch _ _))
    | with_reducible apply cleanup_link
    | with_reducible apply keep_bind _ _ (keep _ (linked_access _))
    | with_reducible apply keep_bind _ _ (keep _ (linked_lift _))
    | with_reducible apply PrefixEnsures.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
    | (simp only [bind_assoc,pure_bind]))

theorem poll_tail_link (pid : PeerId) (budget : Nat) (acc : Nat × Gro × Bool) :
    PrefixEnsures (Context base acc.2.1) (Linked base)
      (do
        if !acc.2.2 && acc.1 < budget then liftPrefix (invariant "the rx_queue did not drain")
        if ← liftPrefix (branch .rxPollComplete (acc.1 < budget)) then
          access (completeAccess pid)
          flushAll acc.2.1
        else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
        return acc.1)
      (fun _ h _ => Linked base h) := by
  rx_link_step
  exact PrefixEnsures.pure (P := fun h _ => Linked base h) (fun _ _ hi => hi) (fun _ _ hi => hi)

set_option maxHeartbeats 2000000 in
/-- The unchanged poll discharges selection linkage from its actual getter
and peer guard. Failed prefixes keep only ordered historical witnesses. -/
theorem poll_link (pid : PeerId) (budget : Nat) :
    PrefixEnsures (Context base {}) (Linked base) (poll pid budget) (fun _ h _ => Linked base h) := by
  unfold poll
  apply keep_bind _ _ (keep _ (linked_lift _))
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi.1)
  · apply PrefixEnsures.bind (Q := fun acc : Nat × Gro × Bool => Context base acc.2.1)
    · with_reducible apply (PrefixEnsures.rangeInvariant _ (0, ({} : Gro), false) _
        (fun acc : Nat × Gro × Bool => Context base acc.2.1) (Linked base) (fun _ _ _ hi => hi.1))
      intro index acc
      rx_link_step
    · intro acc
      exact poll_tail_link pid budget acc

/-- A fresh metadata journal needs no World or allocation premise. Its prior
lifetime history is exactly the existing observer's input. -/
theorem poll_seed_link (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    Linked (seed prior) (runPrefix (poll pid budget) w (seed prior)).2 := by
  exact (poll_link (base := seed prior) pid budget w (seed prior)
    ⟨Linked.start,by simp [Supported]⟩).choose_spec.2.1

/-- Every witness lies within the actual new suffix. Arbitrary incoming
metadata cannot supply an earlier consumed, buffered or entered event. -/
theorem poll_suffix_link (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    ∃ suffix, (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix ∧ Linked [] suffix := by
  obtain ⟨s,hs,hl⟩ := (poll_seed_link pid budget w prior).rebase []
  exact ⟨s,hs,by simpa only [List.nil_append] using hl⟩

/-- The exact event and full receipt/Entry are supported by a strict prefix
of this same execution's suffix, including on a failed poll prefix. -/
theorem poll_ordered_links (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent) :
    ∃ suffix, (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix ∧
      Linked [] suffix ∧ ∀ event ∈ suffix, ∃ before after,
        suffix = before ++ [event] ++ after ∧ EventLink [] before event := by
  obtain ⟨s,hs,hl⟩ := poll_suffix_link pid budget w prior
  obtain ⟨t,ht,he⟩ := hl.events
  simp only [List.nil_append] at ht he
  subst t
  exact ⟨s,hs,hl,he⟩

/-- Decode only committed poll/access events; audit probe markers remain in
the actual persistent history and are irrelevant to receipt ordering. -/
def historyEvent : RxHistory.Event → Option RxJoint.Event
  | .audit (.lifetime e) => some (.access e)
  | .audit (.probe _) => none
  | .removed n skb stamp => some (.removed n skb stamp)
  | .checkedState n skb stamp pkt r => some (.checkedState n skb stamp pkt r)
  | .checkedCounter n skb stamp pkt r => some (.checkedCounter n skb stamp pkt r)
  | .checkedEndpoint n skb stamp pkt r => some (.checkedEndpoint n skb stamp pkt r)
  | .consumed n skb stamp r => some (.consumed n skb stamp r)
  | .buffered e => some (.buffered e)
  | .entered e => some (.entered e)
  | .completed e r => some (.completed e r)

theorem promote_history (s : List RxJoint.Event) :
    (s.map RxHistory.promote).filterMap historyEvent = s :=
  filterMap_encoded RxHistory.promote historyEvent (by intro e; cases e <;> rfl) s

def HistoryLinked (h : List RxHistory.Event) : Prop := Linked [] (h.filterMap historyEvent)

/-- Promotion uses the actual prior audit/lifetime seed, retains all old
interleaved probes, and appends only this poll's linked suffix. -/
theorem observePoll_link_suffix (pid : PeerId) (budget : Nat) (w : World) (h : List RxHistory.Event) :
    ∃ suffix,
      (runPrefix (poll pid budget) w (seed (RxHistory.prior h))).2 = seed (RxHistory.prior h) ++ suffix ∧
      runPrefix (RxHistory.observePoll pid budget) w h =
        ((runPrefix (poll pid budget) w (seed (RxHistory.prior h))).1,h ++ suffix.map RxHistory.promote) ∧
      Linked [] suffix := by
  obtain ⟨s,hs,hl⟩ := poll_suffix_link pid budget w (RxHistory.prior h)
  exact ⟨s,hs,RxHistory.observePoll_suffix pid budget w h _ s (Prod.ext rfl hs),hl⟩

theorem observePoll_link (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h _ => HistoryLinked h) HistoryLinked (RxHistory.observePoll pid budget) := by
  intro w h hi
  obtain ⟨s,hs,he,hl⟩ := observePoll_link_suffix pid budget w h
  have linked : HistoryLinked (h ++ s.map RxHistory.promote) := by
    unfold HistoryLinked
    rw [List.filterMap_append,promote_history]
    exact hi.append hl
  refine ⟨s.map RxHistory.promote,by rw [he],by simpa only [he] using linked,?_⟩
  rw [he]
  cases (runPrefix (poll pid budget) w (seed (RxHistory.prior h))).1 <;> trivial

/-- Finite sequential polls retain receipt ordering on every prefix. This
uses the existing operation; it adds no observer or caller hierarchy. -/
theorem polls_link (calls : List (PeerId × Nat)) :
    PrefixPreserves (fun h _ => HistoryLinked h) HistoryLinked (RxHistory.polls calls) := by
  unfold RxHistory.polls
  apply PrefixPreserves.forM (I := fun h _ => HistoryLinked h) (S := HistoryLinked)
  · exact fun _ _ hi => hi
  · intro call
    change PrefixPreserves (fun h _ => HistoryLinked h) HistoryLinked
      (RxHistory.observePoll call.1 call.2 >>= fun _ => pure ())
    apply PrefixPreserves.bind (observePoll_link call.1 call.2)
    intro n
    exact PrefixPreserves.pure (I := fun h _ => HistoryLinked h)
      (S := HistoryLinked) (fun _ _ hi => hi) ()

end Leanux.Proofs.WG.Queues.RxLink
