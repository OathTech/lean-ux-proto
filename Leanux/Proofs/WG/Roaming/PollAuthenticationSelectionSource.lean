import Leanux.Proofs.WG.Roaming.PollAuthenticationBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes RxJoint

variable {α : Type}

theorem checks_append {history : List RxHistory.Event} {h t : List Event}
    (left : Checks history h) (right : Checks history t) : Checks history (h++t) := by
  intro e member
  exact (List.mem_append.mp member).elim (left e) (right e)

theorem checks_emit (history : List RxHistory.Event) (e : Event)
    (facts : EventFacts history e) :
    PrefixPreserves (fun h _=>Checks history h) (Checks history)
      (emitPrefix (State:=World) e) := by
  intro w h hi
  have next := checks_append hi (show Checks history [e] from by
    intro x member
    cases List.mem_singleton.mp member
    exact facts)
  exact ⟨[e],rfl,next,next⟩

theorem checks_lift (history : List RxHistory.Event) (action : Leanux.M α) :
    PrefixPreserves (fun h _=>Checks history h) (Checks history) (liftPrefix action) := by
  intro w h hi
  refine ⟨[],by simp,hi,?_⟩
  simp only [runPrefix_lift]
  cases action.run w <;> trivial

theorem checks_access (history : List RxHistory.Event) (action : PrefixM LifetimeEvent α) :
    PrefixPreserves (fun h _=>Checks history h) (Checks history) (access action) := by
  intro w h hi
  let suffix := ((runPrefix action w (h.filterMap accessEvent)).2.drop
    (h.filterMap accessEvent).length).map Event.access
  have next : Checks history (h++suffix) := checks_append hi (by
    intro e member
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp member
    trivial)
  refine ⟨suffix,rfl,next,?_⟩
  cases (runPrefix (access action) w h).1 <;> trivial

theorem checks_receipt (history : List RxHistory.Event) (action : Obs α)
    (event : RunWitness α→Event)
    (checked : PrefixPreserves (fun h _=>Checks history h) (Checks history) action)
    (facts : ∀r,EventFacts history (event r)) :
    PrefixPreserves (fun h _=>Checks history h) (Checks history)
      (receiptObserved action event) := by
  unfold receiptObserved
  exact checked.captureObserved.bind (fun r=>(checks_emit history _ (facts r)).bind
    (fun _=>PrefixPreserves.pure (I:=fun h (_:World)=>Checks history h) (fun _ _ hi=>hi) _))

theorem keep (history : List RxHistory.Event) (action : Obs α) (original : Leanux.M α)
    (checked : PrefixPreserves (fun h _=>Checks history h) (Checks history) action)
    (erases : ErasesPrefix action original)
    (preserves : Preserves (fun w : World=>PublicationHistory.Inv history w.wg) original) :
    PrefixPreserves (State history) (Checks history) action := by
  intro w h hi
  obtain ⟨suffix,append,safe,_⟩ := checked w h hi.2
  refine ⟨suffix,append,safe,?_⟩
  cases result : (runPrefix action w h).1 with
  | error stop => trivial
  | ok out =>
    exact ⟨(hoare_iff_run _ _ _).mp preserves w out.1 out.2 hi.1
      ((erases w h).symm.trans result),safe⟩

theorem lifted (history : List RxHistory.Event) (action : Leanux.M α)
    (preserves : Preserves (fun w : World=>PublicationHistory.Inv history w.wg) action) :
    PrefixPreserves (State history) (Checks history) (liftPrefix action) :=
  keep history _ action (checks_lift history action) (erasesPrefix_lift _) preserves

theorem native_access (history : List RxHistory.Event) (action : MixedM α)
    (original : WG.M α) (erases : ErasesStatePrefix action original)
    (preserves : Preserves (PublicationHistory.Inv history) original) :
    PrefixPreserves (State history) (Checks history) (access (liftWGObserver action)) :=
  keep history _ _ (checks_access history _) (access_erases (liftWGObserver_erases erases))
    (PublicationPoll.native_product _ _ preserves)

theorem selected_keep (history : List RxHistory.Event) (id : SkbId)
    (stamp : PacketStamp) (pkt : RxPacket) (action : Obs α) (original : Leanux.M α)
    (kept : PrefixPreserves (State history) (Checks history) action)
    (erases : ErasesPrefix action original) (frame : SameView RxDisposition.rxStore original) :
    PrefixPreserves (Selected history id stamp pkt) (Checks history) action := by
  intro w h hi
  obtain ⟨suffix,append,safe,normal⟩ := kept w h hi.1
  refine ⟨suffix,append,safe,?_⟩
  cases result : (runPrefix action w h).1 with
  | error stop => trivial
  | ok out =>
    exact ⟨by simpa only [result] using normal,
      RxDisposition.selected_transport id stamp pkt w out.2
        ((ProjectedAction.iff_run _ _ _).mp frame w out.1 out.2
          ((erases w h).symm.trans result)) hi.2⟩

theorem captured (history : List RxHistory.Event) (id : SkbId) :
    PrefixEnsures (State history) (Checks history) (capture id)
      (fun out=>Selected history id out.2 out.1) := by
  have checked : PrefixPreserves (fun h _=>Checks history h) (Checks history) (capture id) := by
    intro w h hi
    obtain ⟨suffix,append,safe,_⟩ := checks_access history (liftWGObserver (getRxSkbPrefix id)) w h hi
    refine ⟨suffix,append,safe,?_⟩
    cases (runPrefix (capture id) w h).1 <;> trivial
  intro w h hi
  obtain ⟨suffix,append,safe,_⟩ := checked w h hi.2
  refine ⟨suffix,append,safe,?_⟩
  cases result : (runPrefix (capture id) w h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨same,selected⟩ := RxDisposition.capture_selected id w out.2 h out.1.1 out.1.2 result
    exact ⟨⟨same ▸ hi.1,safe⟩,selected⟩

theorem dropped (history : List RxHistory.Event) (pid n id : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Selected history id stamp pkt) (Checks history) (drop pid n id stamp) := by
  have erases : ErasesPrefix (drop pid n id stamp) (liftWG (dropRxQueue pid)) := by
    intro w h
    have erased := access_erases (liftWGObserver_erases (rxDropPeekedPrefix_erases pid)) w h
    unfold drop
    rw [runPrefix_bind]
    cases run : runPrefix (access (liftWGObserver (rxDropPeekedPrefix pid))) w h with
    | mk result t =>
      cases result with
      | error stop => simpa only [run,dropRxQueue] using erased
      | ok out => cases out.1; simpa only [run,runPrefix_emit,dropRxQueue] using erased
  apply selected_keep history id stamp pkt _ (liftWG (dropRxQueue pid))
  · apply keep history _ _
      ((checks_access history _).bind (fun _=>checks_emit history (.removed n id stamp) True.intro))
      erases
    exact PublicationPoll.native_product _ _ (PublicationPoll.drop_preserves pid history)
  · exact erases
  · exact RxDisposition.drop_rxStore pid

theorem selected_ambient (history : List RxHistory.Event) (id : SkbId)
    (stamp : PacketStamp) (pkt : RxPacket) (site : Decision) (b : Bool) :
    PrefixPreserves (Selected history id stamp pkt) (Checks history) (liftPrefix (branch site b)) :=
  selected_keep history id stamp pkt _ _ (lifted history _
    (productAmbient_spec (AmbientM.branch site b) _ (fun _ _ hi=>hi)))
    (erasesPrefix_lift _)
    ((show SameProductStore (branch site b : Leanux.M Bool) from
      fun _=>productAmbient_spec (AmbientM.branch site b) _ (fun _ _ hi=>hi)).of_factor
        (fun s : ProductStore43=>(s.2.2.2.dev.map (·.ifindex),
          fun id : SkbId=>s.2.2.2.dev.bind fun d=>d.rxSkbs[id]?)) _ (fun _=>rfl))

theorem selected_counter (history : List RxHistory.Event) (n id : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixPreserves (Selected history id stamp pkt) (Checks history)
      (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (Event.checkedCounter n id stamp pkt)) := by
  apply selected_keep history id stamp pkt _ (liftWG (counterValidate pkt.keypair pkt.nonce))
  · apply keep history _ _
      (checks_receipt history _ (Event.checkedCounter n id stamp pkt) (checks_access history _) (fun _=>True.intro))
      (RxLink.receipt_erases (access_erases
        (liftWGObserver_erases (counterValidatePrefix_erases _ _))))
    exact PublicationPoll.native_product _ _ (PublicationPoll.counterValidate_preserves _ _ history)
  · exact RxLink.receipt_erases (access_erases
      (liftWGObserver_erases (counterValidatePrefix_erases _ _)))
  · exact RxDisposition.counter_rxStore _ _

theorem selected_state (history : List RxHistory.Event) (n id : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixEnsures (Selected history id stamp pkt) (Checks history)
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState n id stamp pkt))
      (fun b h w=>Selected history id stamp pkt h w ∧ b=(pkt.state != .crypted)) := by
  have kept : PrefixPreserves (Selected history id stamp pkt) (Checks history)
      (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState n id stamp pkt)) := by
    apply selected_keep history id stamp pkt _ (branch .rxPollNotCrypted (pkt.state != .crypted))
    · apply keep history _ _
        (checks_receipt history _ (Event.checkedState n id stamp pkt) (checks_lift history _) (fun _=>True.intro))
        (RxLink.receipt_erases (erasesPrefix_lift _))
      exact productAmbient_spec (AmbientM.branch _ _) _ (fun _ _ hi=>hi)
    · exact RxLink.receipt_erases (erasesPrefix_lift _)
    · exact (show SameProductStore (branch .rxPollNotCrypted (pkt.state != .crypted) : Leanux.M Bool) from
        fun _=>productAmbient_spec (AmbientM.branch _ _) _ (fun _ _ hi=>hi)).of_factor
          (fun s : ProductStore43=>(s.2.2.2.dev.map (·.ifindex),
            fun id : SkbId=>s.2.2.2.dev.bind fun d=>d.rxSkbs[id]?)) _ (fun _=>rfl)
  intro w h hi
  obtain ⟨suffix,append,safe,normal⟩ := kept w h hi
  exact ⟨suffix,append,safe,normal,rfl⟩

theorem endpoint (history : List RxHistory.Event) (n id : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (crypted : pkt.state=.crypted) :
    PrefixEnsures (Selected history id stamp pkt) (Checks history)
      (receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
        (Event.checkedEndpoint n id stamp pkt)) (fun _=>State history) := by
  intro w h hi
  rw [runPrefix_receiptObserved,runPrefix_lift]
  cases result : (liftWG (endpointFromSkb pkt.source)).run w with
  | error stop => exact ⟨[],by simp,hi.1.2,True.intro⟩
  | ok out =>
    let event := Event.checkedEndpoint n id stamp pkt ⟨out.1,w,out.2⟩
    have next : Checks history (h++[event]) := checks_append hi.1.2 (by
      intro e member
      cases List.mem_singleton.mp member
      exact ⟨hi.1.1,hi.2,crypted⟩)
    have kept := (hoare_iff_run _ _ _).mp
      (PublicationPoll.native_product _ _
        ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationPoll.«0».Leanux.Proofs.WG.PublicationPoll.store)
          _ (endpointFromSkb_sameWGStore pkt.source) history)) w out.1 out.2 hi.1.1 result
    exact ⟨[event],rfl,next,kept,next⟩

end Leanux.Proofs.WG.Roaming.PollAuthentication
