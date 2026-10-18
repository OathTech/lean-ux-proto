import Leanux.Proofs.WG.AuthenticatedEffects.TransportEntryChecks

/-! Live selected-cell linkage at the existing pre-consume replay receipt.
No extra getter or synthetic source event is introduced. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues RxJoint RxDisposition
set_option maxHeartbeats 2000000
variable {id : SkbId} {stamp : PacketStamp} {pkt : RxPacket}

def selectedEntry : RxJoint.Event → Option (SkbId × PacketStamp × RxPacket × RunWitness Bool)
  | .checkedCounter _ id stamp pkt r => some (id,stamp,pkt,r)
  | _ => none

def Checks (h : List RxJoint.Event) : Prop :=
  ∀ e ∈ h.filterMap selectedEntry, SelectedAt e.1 e.2.1 e.2.2.1 e.2.2.2.before

def Base (h : List RxJoint.Event) (_ : World) := Checks h

def Picked (id : SkbId) (stamp : PacketStamp) (pkt : RxPacket)
    (h : List RxJoint.Event) (w : World) := Checks h ∧ SelectedAt id stamp pkt w

private theorem frame (g : Obs α) (appends : Appends g) (quiet : HistoryFrame selectedEntry g) :
    PrefixPreserves Base Checks g := by
  intro w h hi
  obtain ⟨s,hs⟩ := appends w h
  have safe : Checks (runPrefix g w h).2 := by unfold Checks; rw [quiet w h]; exact hi
  refine ⟨s,hs,safe,?_⟩
  cases (runPrefix g w h).1 <;> trivial

private theorem access_frame (a : PrefixM LifetimeEvent α) : HistoryFrame selectedEntry (access a) :=
  fun w h => focusPrefix_other RxJoint.Event.access accessEvent selectedEntry (fun _ => rfl) a w h

private theorem consume_frame (pid n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    HistoryFrame selectedEntry (consume pid n id stamp pkt ep) := by
  unfold consume
  apply (access_frame _).captureObserved.bind
  intro r
  apply (HistoryFrame.emit _ rfl).bind
  intro doneUnit
  cases r.value with
  | none => exact HistoryFrame.pure _ _
  | some bytes => exact (HistoryFrame.emit _ rfl).bind (fun _ => HistoryFrame.pure _ _)

private theorem enter_frame (e : Entry) : HistoryFrame selectedEntry (enter e) := by
  unfold enter
  exact (HistoryFrame.emit _ rfl).bind (fun _ => (access_frame _).receiptObserved (fun _ => rfl))

private theorem flush_frame (es : List Entry) : HistoryFrame selectedEntry (flush es) := by
  induction es with
  | nil => exact HistoryFrame.pure _ _
  | cons e es ih =>
    simp only [flush,List.forM_eq_forM,List.forM_cons] at *
    exact (enter_frame e).bind (fun _ => ih)

private theorem normalList_frame (g : Gro) : HistoryFrame selectedEntry (normalList g) := by
  unfold normalList
  split
  · exact HistoryFrame.pure _ _
  · exact (flush_frame _).bind (fun _ => HistoryFrame.pure _ _)

private theorem normalOne_frame (g : Gro) (e : Entry) (n : Nat) :
    HistoryFrame selectedEntry (normalOne g e n) := by
  unfold normalOne
  dsimp only
  split
  · exact normalList_frame _
  · exact HistoryFrame.pure _ _

private theorem receive_frame (g : Gro) (e : Entry) : HistoryFrame selectedEntry (receive g e) := by
  unfold receive
  repeat' first
    | exact normalOne_frame _ _ _
    | exact HistoryFrame.pure _ _
    | exact HistoryFrame.lift _ _
    | with_reducible apply HistoryFrame.bind
    | (keypairs_intro_forall; try dsimp only)
    | (with_reducible split <;> try dsimp only)

private theorem flushAll_frame (g : Gro) : HistoryFrame selectedEntry (flushAll g) := by
  unfold flushAll
  apply HistoryFrame.bind
  · apply HistoryFrame.forIn
    intro e g
    exact (normalOne_frame _ _ _).bind (fun _ => HistoryFrame.pure _ _)
  · intro g
    exact (normalList_frame _).bind (fun _ => HistoryFrame.pure _ _)

private theorem capture_rule (id : SkbId) :
    PrefixEnsures Base Checks (capture id) (fun out => Picked id out.2 out.1) := by
  intro w h hi
  rw [capture_run]
  cases hr : (liftWG (getRxSkb id)).run w with
  | error e => exact ⟨[],by simp,hi,True.intro⟩
  | ok out =>
    rcases out with ⟨pkt,v⟩
    have cap : (runPrefix (capture id) w h).1 = .ok ((pkt,packetStamp w.wg id),v) := by
      rw [capture_run,hr]
    obtain ⟨same,selected⟩ := capture_selected id w v h pkt (packetStamp w.wg id) cap
    have safe : Checks (h ++ [.access (.packet (.read (.inr id) (packetStamp w.wg id)))]) := by
      simpa only [Checks,List.filterMap_append,List.filterMap_cons,selectedEntry,
        List.filterMap_nil,List.append_nil,Base] using hi
    exact ⟨[_],rfl,safe,safe,selected⟩

private theorem picked_keep (g : Obs α) (original : Leanux.M α)
    (appends : Appends g) (quiet : HistoryFrame selectedEntry g)
    (erases : ErasesPrefix g original) (same : SameView rxStore original) :
    PrefixPreserves (Picked id stamp pkt) Checks g := by
  intro w h hi
  obtain ⟨s,hs,safe,_⟩ := frame g appends quiet w h hi.1
  refine ⟨s,hs,safe,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    exact ⟨safe,selected_transport id stamp pkt w out.2
      ((ProjectedAction.iff_run _ _ _).mp same w out.1 out.2 ((erases w h).symm.trans hr)) hi.2⟩

private theorem drop_rule (pid n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Picked id stamp pkt) Checks (drop pid n id stamp) := by
  unfold drop
  apply PrefixPreserves.bind (picked_keep _ _ (access_appends _) (access_frame _)
    (access_erases (liftWGObserver_erases (rxDropPeekedPrefix_erases pid))) (drop_rxStore pid))
  intro doneUnit w h hi
  have safe : Checks (h ++ [.removed n id stamp]) := by
    simpa only [Checks,List.filterMap_append,List.filterMap_cons,selectedEntry,
      List.filterMap_nil,List.append_nil] using hi.1
  exact ⟨[_],rfl,safe,safe,hi.2⟩

private theorem picked_lift (a : Leanux.M α) (same : SameView rxStore a) :
    PrefixPreserves (Picked id stamp pkt) Checks (liftPrefix a) :=
  picked_keep _ a (Appends.lift a) (HistoryFrame.lift _ a) (erasesPrefix_lift a) same

private theorem state_rule (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Picked id stamp pkt) Checks
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState n id stamp pkt)) := by
  refine picked_keep _ (branch .rxPollNotCrypted (pkt.state != .crypted)) ?_ ?_ ?_ ?_
  · exact (Appends.lift _).receiptObserved
  · exact (HistoryFrame.lift _ _).receiptObserved (fun _ => rfl)
  · exact RxLink.receipt_erases (erasesPrefix_lift _)
  · exact fun initial => productAmbient_spec (AmbientM.branch _ _) _ (fun _ _ hi => hi)

private theorem counter_rule (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixEnsures (Picked id stamp pkt) Checks
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (Event.checkedCounter n id stamp pkt)) (fun _ => Base) := by
  unfold receiptObserved
  apply PrefixEnsures.bind (PrefixEnsures.captureObserved (picked_keep _ _
    (access_appends _) (access_frame _)
    (access_erases (liftWGObserver_erases (counterValidatePrefix_erases _ _)))
    (counter_rxStore _ _)))
  intro r w h hi
  have current : Picked id stamp pkt h w := hi.1 ▸ hi.2.1
  obtain ⟨before,prior,_⟩ := hi.2.2
  have safe : Checks (h ++ [Event.checkedCounter n id stamp pkt r]) := by
    intro entry member
    rw [List.filterMap_append,List.mem_append] at member
    rcases member with old | fresh
    · exact current.1 entry old
    · have eq : entry = (id,stamp,pkt,r) := by simpa only [List.filterMap_cons,
        selectedEntry,List.filterMap_nil,List.mem_singleton] using fresh
      subst entry
      exact prior.2
  exact ⟨[_],rfl,safe,safe⟩

private theorem keep_bind (g : Obs α) (f : α → Obs β)
    (hg : PrefixPreserves I Checks g) (hf : ∀ x, PrefixEnsures I Checks (f x) Q) :
    PrefixEnsures I Checks (g >>= f) Q := PrefixEnsures.bind hg hf

private theorem cleanup (kp : Option KeypairId) (now : Bool) (f : Unit → Obs α)
    (hf : PrefixEnsures Base Checks (access (liftWGObserver (keypairPutPrefix kp now)) >>= f) Q) :
    PrefixEnsures (Picked id stamp pkt) Checks
      (access (liftWGObserver (keypairPutPrefix kp now)) >>= f) Q :=
  hf.consequence (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

private theorem stop (a : Leanux.M Unit) (stops : ∀ w, ∃ e, a.run w = .error e)
    (safe : ∀ h w, P h w → Checks h) (f : Unit → Obs α) :
    PrefixEnsures P Checks (liftPrefix a >>= f) Q := by
  intro w h hi
  obtain ⟨e,he⟩ := stops w
  simp only [runPrefix_bind,runPrefix_lift,he]
  exact ⟨[],by simp,safe h w hi,True.intro⟩

macro "transport_selection_step" : tactic => `(tactic| first
  | rx_phase_reduce
  | (first | rx_phase_head plain invariant | rx_phase_head plain unsupported
     apply stop _ (fun _ => ⟨_,rfl⟩)
     exact fun _ _ hi => hi.1)
  | (rx_phase_head plain Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi) (fun _ _ hi => hi))
  | (rx_phase_head plain capture; apply PrefixEnsures.bind (capture_rule _))
  | (rx_phase_head plain drop; apply keep_bind _ _ (drop_rule _ _ _ _ _))
  | (rx_phase_head receipt branch; apply keep_bind _ _ (state_rule _ _ _ _))
  | (rx_phase_head receipt counterValidatePrefix; apply PrefixEnsures.bind (counter_rule _ _ _ _))
  | (rx_phase_head receipt endpointFromSkb; apply keep_bind _ _ (frame _ (Appends.lift _).receiptObserved
      ((HistoryFrame.lift _ _).receiptObserved (fun _ => rfl))))
  | (rx_phase_head plain keypairPutPrefix; apply cleanup)
  | (rx_phase_head plain consume; apply keep_bind _ _ (frame _ (consume_appends _ _ _ _ _ _) (consume_frame _ _ _ _ _ _)))
  | (rx_phase_head plain receive; apply keep_bind _ _ (frame _ (receive_appends _ _) (receive_frame _ _)))
  | (rx_phase_head plain flushAll; apply keep_bind _ _ (frame _ (flushAll_appends _) (flushAll_frame _)))
  | (rx_phase_head plain access; apply keep_bind _ _ (frame _ (access_appends _) (access_frame _)))
  | (rx_phase_head plain branch; first
      | apply keep_bind _ _ (picked_lift _ (fun initial => productAmbient_spec (AmbientM.branch _ _) _ (fun _ _ hi => hi)))
      | apply keep_bind _ _ (frame _ (Appends.lift _) (HistoryFrame.lift _ _)))
  | (rx_phase_head plain liftPrefix; apply keep_bind _ _ (frame _ (Appends.lift _) (HistoryFrame.lift _ _)))
  | (rx_phase_head plain ite; apply PrefixEnsures.ite)
  | rx_phase_intro
  | rx_phase_match)

theorem poll (pid : PeerId) (budget : Nat) :
    PrefixPreserves Base Checks (RxJoint.poll pid budget) := by
  unfold RxJoint.poll
  repeat' first
    | exact fun _ _ hi => hi
    | transport_selection_step
    | (rx_phase_head plain ForIn.forIn
       apply keep_bind _ _
       first | apply PrefixPreserves.range | apply PrefixPreserves.forIn)

/-- Actual selection survives capture, queue removal and the intervening
guards until the existing replay-check receipt is emitted. No incoming-world
premise is needed, and later Stop does not discard the receipt. -/
theorem poll_selected (pid : PeerId) (budget : Nat) (w : World) (prior : List LifetimeEvent)
    (occurrence id : Nat) (stamp : PacketStamp) (pkt : RxPacket) (r : RunWitness Bool)
    (member : Event.checkedCounter occurrence id stamp pkt r ∈
      (runPrefix (RxJoint.poll pid budget) w (seed prior)).2) :
    SelectedAt id stamp pkt r.before := by
  have initial : Base (seed prior) w := by
    intro entry member
    have empty : (seed prior).filterMap selectedEntry = [] :=
      filterMap_disjoint Event.access selectedEntry (fun _ => rfl) prior
    rw [empty] at member
    cases member
  have checked := (poll pid budget w (seed prior) initial).choose_spec.2.1
  exact checked (id,stamp,pkt,r) (List.mem_filterMap.mpr ⟨_,member,rfl⟩)

end Leanux.Proofs.WG.AuthenticatedEffects.TransportSelection
