import Leanux.Proofs.WG.Roaming.RemoteChronologyPollBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Poll
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem relative_tracks {E α : Type} {effect : Effect E} {observed : PrefixM E α}
    (relative : Relative effect observed) (entry : RemoteMap) :
    PrefixPreserves (Tracks effect entry) (fun _ => True) observed := by
  intro w h prior
  obtain ⟨suffix,appended,normal⟩ := relative w h
  refine ⟨suffix,appended,True.intro,?_⟩
  cases run : (runPrefix observed w h).1 with
  | error stop => trivial
  | ok out =>
    simp only [run] at normal
    change Last effect entry _ _
    rw [appended]
    exact append prior normal

theorem relative_suffixTracks {E α : Type} {effect : Effect E} {observed : PrefixM E α}
    (relative : Relative effect observed) (entry : RemoteMap) (base : List E) :
    PrefixPreserves (SuffixTracks effect entry base) (fun _ => True) observed := by
  intro w h prior
  obtain ⟨before,was,prior⟩ := prior
  obtain ⟨suffix,appended,normal⟩ := relative w h
  refine ⟨suffix,appended,True.intro,?_⟩
  cases run : (runPrefix observed w h).1 with
  | error stop => trivial
  | ok out =>
    simp only [run] at normal
    exact ⟨before ++ suffix,by rw [appended,was,List.append_assoc],append prior normal⟩

theorem relative_of_suffixTracks {E α : Type} {effect : Effect E} {observed : PrefixM E α}
    (preserved : ∀ entry base,
      PrefixPreserves (SuffixTracks effect entry base) (fun _ => True) observed) :
    Relative effect observed := by
  intro w h
  have initial : SuffixTracks effect (destinationAt w.wg) h h w :=
    ⟨[],by simp,nil_of_retained effect (.refl _)⟩
  obtain ⟨suffix,appended,_,normal⟩ := preserved (destinationAt w.wg) h w h initial
  refine ⟨suffix,appended,?_⟩
  cases run : (runPrefix observed w h).1 with
  | error stop => trivial
  | ok out =>
    simp only [run] at normal
    obtain ⟨actual,shape,tracked⟩ := normal
    have same : suffix = actual := List.append_cancel_left (appended.symm.trans shape)
    exact same ▸ tracked

theorem quiet_relative {E α : Type} (effect : Effect E)
    (observed : PrefixM E α) (action : Leanux.M α)
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (inert : ∀ w h pid, (runPrefix observed w h).2.filterMap (fun e => effect e pid) =
      h.filterMap (fun e => effect e pid))
    (keep : ∀ initial, Preserves (RemotePoll.ProductRetained initial) action) :
    Relative effect observed := by
  intro w h
  obtain ⟨suffix,appended,untouched⟩ := inert_suffix effect observed appends inert w h
  refine ⟨suffix,appended,?_⟩
  cases run : (runPrefix observed w h).1 with
  | error stop => trivial
  | ok out =>
    have retained := (hoare_iff_run _ _ _).mp (keep (destinationAt w.wg))
      w out.1 out.2 (RemoteRetained.refl _) ((erases w h).symm.trans run)
    exact quiet_append (nil_of_retained effect (.refl _)) untouched retained

theorem quiet {E α : Type} (effect : Effect E) (entry : RemoteMap)
    (observed : PrefixM E α) (action : Leanux.M α)
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (inert : ∀ w h pid, (runPrefix observed w h).2.filterMap (fun e => effect e pid) =
      h.filterMap (fun e => effect e pid))
    (keep : ∀ initial, Preserves (RemotePoll.ProductRetained initial) action) :
    PrefixPreserves (Tracks effect entry) (fun _ => True) observed :=
  relative_tracks (quiet_relative effect observed action appends erases inert keep) entry

theorem access_inert {α : Type} (observed : PrefixM LifetimeEvent α) :
    ∀ w h pid, (runPrefix (RxJoint.access observed) w h).2.filterMap
      (fun e => localEffect e pid) = h.filterMap (fun e => localEffect e pid) :=
  fun w h pid => focusPrefix_other RxJoint.Event.access RxJoint.accessEvent
    (fun e => localEffect e pid) (fun _ => rfl) observed w h

theorem access_retained {α : Type} (entry : RemoteMap)
    (observed : PrefixM LifetimeEvent α) (action : Leanux.M α)
    (erases : ErasesPrefix observed action)
    (keep : ∀ initial, Preserves (RemotePoll.ProductRetained initial) action) :
    PrefixPreserves (Tracks localEffect entry) (fun _ => True) (RxJoint.access observed) :=
  quiet localEffect entry _ _ (RxJoint.access_appends _)
    (RxJoint.access_erases erases) (access_inert observed) keep

theorem joint_native {α : Type} (entry : RemoteMap) (observed : MixedM α) (action : WG.M α)
    (erases : ErasesStatePrefix observed action)
    (keep : ∀ initial, Preserves (RemoteSilent.Retained initial) action) :
    PrefixPreserves (Tracks localEffect entry) (fun _ => True)
      (RxJoint.access (liftWGObserver observed)) :=
  access_retained entry _ _ (liftWGObserver_erases erases)
    (fun initial => PublicationPoll.native_product _ _ (keep initial))

theorem lift_retained {E α : Type} (effect : Effect E) (entry : RemoteMap)
    (action : Leanux.M α)
    (keep : ∀ initial, Preserves (RemotePoll.ProductRetained initial) action) :
    PrefixPreserves (Tracks effect entry) (fun _ => True) (liftPrefix action) :=
  quiet effect entry _ action (Appends.lift _) (erasesPrefix_lift _)
    (fun _ _ _ => rfl) keep

theorem ambient {E α : Type} (effect : Effect E) (entry : RemoteMap)
    (action : AmbientM α) :
    PrefixPreserves (Tracks effect entry) (fun _ => True) (liftPrefix (liftAmbient action)) :=
  lift_retained effect entry _ (fun _ => productAmbient_spec action _ (fun _ _ prior => prior))

theorem append_inert {E : Type} {effect : Effect E} {entry : RemoteMap}
    {h : List E} {w : World} (prior : Tracks effect entry h w) (event : E)
    (inert : ∀ pid, effect event pid = none) : Tracks effect entry (h ++ [event]) w := by
  apply quiet_append prior ?_ (.refl _)
  intro pid e member
  have same : e = event := by simpa using member
  subst e
  exact inert pid

theorem emitted {E : Type} (effect : Effect E) (entry : RemoteMap) (event : E)
    (inert : ∀ pid, effect event pid = none) :
    PrefixPreserves (Tracks effect entry) (fun _ => True) (emitPrefix event) :=
  RxJoint.GroSource.emit_preserves (fun _ _ _ => True.intro) event
    (fun _ _ prior => append_inert prior event inert)

theorem receipt {E α : Type} (effect : Effect E) (entry : RemoteMap)
    (observed : PrefixM E α) (event : RunWitness α → E)
    (keep : PrefixPreserves (Tracks effect entry) (fun _ => True) observed)
    (inert : ∀ r pid, effect (event r) pid = none) :
    PrefixPreserves (Tracks effect entry) (fun _ => True) (receiptObserved observed event) :=
  RxJoint.GroSource.receipt_preserves (fun _ _ _ => True.intro) observed event keep
    (fun _ _ _ _ _ _ _ prior => append_inert prior _ (inert _))

theorem capture_tracks (entry : RemoteMap) (skb : SkbId) :
    PrefixPreserves (Tracks localEffect entry) (fun _ => True) (RxJoint.capture skb) := by
  intro w h prior
  obtain ⟨suffix,appended⟩ := RxJoint.capture_appends skb w h
  have inert : ∀ pid, (runPrefix (RxJoint.capture skb) w h).2.filterMap
      (fun e => localEffect e pid) = h.filterMap (fun e => localEffect e pid) :=
    access_inert (liftWGObserver (getRxSkbPrefix skb)) w h
  have untouched := untouched_suffix localEffect h suffix _ appended inert
  refine ⟨suffix,appended,True.intro,?_⟩
  cases run : (runPrefix (RxJoint.capture skb) w h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨pkt,stamp⟩,v⟩ := out
    have same := (RxDisposition.capture_selected skb w v h pkt stamp run).1
    change Last localEffect entry _ _
    rw [same,appended]
    exact quiet_append prior untouched (.refl _)

theorem consume_tracks (entry : RemoteMap) (pid occurrence id : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (Tracks localEffect entry) (fun _ => True)
      (RxJoint.consume pid occurrence id stamp pkt ep) := by
  intro w h prior
  obtain ⟨suffix,appended⟩ := RxJoint.access_appends
    (liftWGObserver (consumeDataDonePrefix pid pkt ep)) w h
  have inert := access_inert (liftWGObserver (consumeDataDonePrefix pid pkt ep)) w h
  have untouched := untouched_suffix localEffect h suffix _ appended inert
  rw [RxJoint.consume_run]
  cases run : runPrefix (RxJoint.access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t =>
    simp only [run] at appended
    cases result with
    | error stop => exact ⟨suffix,appended,True.intro,True.intro⟩
    | ok out =>
      obtain ⟨returned,v⟩ := out
      have native := (RxJoint.access_erases
        (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h).symm.trans
          (congrArg Prod.fst run)
      rw [liftWG_run] at native
      cases original : ((consumeDataDone pid pkt ep).run w.wg).run w.ambient with
      | error stop => simp [original,Except.map] at native
      | ok out =>
        obtain ⟨⟨value,g⟩,after⟩ := out
        simp only [original,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
        obtain ⟨rfl,rfl⟩ := native
        let r : RxDisposition.ConsumeReceipt := ⟨pid,pkt,ep,⟨value,w.wg,g,w.ambient,after⟩⟩
        have changed := Driver.consume_effect occurrence id stamp r original
        have next : Tracks localEffect entry (t ++ [.consumed occurrence id stamp r])
            {w with wg:=g,ambient:=after} := by
          change Last localEffect entry _ _
          rw [appended]
          exact RemoteChronology.receipt (quiet_append prior untouched (.refl _))
            (.consumed occurrence id stamp r) changed
        cases value with
        | none =>
          exact ⟨suffix ++ [_],by simp only [appended,List.append_assoc]; rfl,True.intro,next⟩
        | some bytes =>
          exact ⟨suffix ++ [_,_],by simp only [appended,List.append_assoc]; rfl,True.intro,
            append_inert next _ (fun _ => rfl)⟩

theorem gro_receive_tracks (entry : RemoteMap) (g : RxJoint.Gro) (e : RxJoint.Entry) :
    PrefixPreserves (Tracks localEffect entry) (fun _ => True) (RxJoint.receive g e) := by
  rw [RxJoint.GroSource.receive_factor]
  apply RxJoint.GroSource.receive_preserves id _ (fun _ _ _ => True.intro)
  · intro e h w prior; exact append_inert prior _ (fun _ => rfl)
  · intro bytes
    exact access_retained entry _ _ (stackReceivePrefix_erases bytes)
      (fun initial => RemotePoll.stack_retained initial bytes)
  · intro e w h x v t _ _ prior; exact append_inert prior _ (fun _ => rfl)

theorem gro_flush_tracks (entry : RemoteMap) (g : RxJoint.Gro) :
    PrefixPreserves (Tracks localEffect entry) (fun _ => True) (RxJoint.flushAll g) := by
  rw [RxJoint.GroSource.flushAll_factor]
  apply RxJoint.GroSource.flushAll_preserves id _ (fun _ _ _ => True.intro)
  · intro e h w prior; exact append_inert prior _ (fun _ => rfl)
  · intro bytes
    exact access_retained entry _ _ (stackReceivePrefix_erases bytes)
      (fun initial => RemotePoll.stack_retained initial bytes)
  · intro e w h x v t _ _ prior; exact append_inert prior _ (fun _ => rfl)

theorem poll_tracks (entry : RemoteMap) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Tracks localEffect entry) (fun _ => True) (RxJoint.poll pid budget) := by
  rw [RxJoint.PollSource.poll_factor]
  apply RxJoint.PollSource.poll_preserves (fun {_} a => a) _ _ (fun _ _ _ => True.intro)
  · intro peer; exact joint_native entry _ _ (RxJoint.peekAccess_erases peer)
      (fun initial => (RemotePoll.peek_frame peer).wp (RemoteRetained initial))
  · intro first; exact joint_native entry _ _ (RxJoint.readyAccess_erases first)
      (fun initial => RemotePoll.ready_retained initial first)
  · exact capture_tracks entry
  · intro peer n skb stamp
    unfold RxJoint.drop
    exact (joint_native entry _ _ (rxDropPeekedPrefix_erases peer)
      (fun initial => (RemotePoll.drop_frame peer).wp (RemoteRetained initial))).bind
        (fun _ => emitted localEffect entry _ (fun _ => rfl))
  · intro n skb stamp pkt
    exact receipt localEffect entry _ _
      (ambient localEffect entry (AmbientM.branch .rxPollNotCrypted (pkt.state != .crypted)))
      (fun _ _ => rfl)
  · intro n skb stamp pkt
    exact receipt localEffect entry _ _ (joint_native entry _ _
      (counterValidatePrefix_erases pkt.keypair pkt.nonce)
      (fun initial => RemotePoll.counter_retained initial pkt.keypair pkt.nonce)) (fun _ _ => rfl)
  · intro n skb stamp pkt
    exact receipt localEffect entry _ _ (lift_retained localEffect entry _
      (fun initial => PublicationPoll.native_product _ _
        ((RemoteCompletion.store_remotes (endpointFromSkb_sameWGStore pkt.source)).wp
          (RemoteRetained initial)))) (fun _ _ => rfl)
  · exact consume_tracks entry
  · intro kid; exact joint_native entry _ _ (keypairPutPrefix_erases (some kid) false)
      (fun initial => RemotePoll.keypairPut_retained initial (some kid) false)
  · intro peer; exact joint_native entry _ _ (peerPutMixed_erases (some peer))
      (fun initial => (ensures_iff _ _ _).mp (peerPut_remotes (some peer) initial))
  · intro skb; exact joint_native entry _ _ (freeRxSkbPrefix_erases skb)
      (fun initial => (RemotePoll.packet_frame (SkbStore.freeRx skb)).wp (RemoteRetained initial))
  · intro peer; exact joint_native entry _ _ (RxJoint.completeAccess_erases peer)
      (fun initial => (RemotePoll.complete_frame peer).wp (RemoteRetained initial))
  · intro b; exact ambient localEffect entry (AmbientM.branch .rxPollNoBudget b)
  · intro b; exact ambient localEffect entry (AmbientM.branch .rxPollCounterInvalid b)
  · intro b; exact ambient localEffect entry (AmbientM.branch .rxPollEndpointFailed b)
  · intro b; exact ambient localEffect entry (AmbientM.branch .rxPollFree b)
  · intro b; exact ambient localEffect entry (AmbientM.branch .rxPollBudgetDone b)
  · intro b; exact ambient localEffect entry (AmbientM.branch .rxPollComplete b)
  · exact gro_receive_tracks entry
  · exact gro_flush_tracks entry


theorem history_poll_relative (pid : PeerId) (budget : Nat) :
    Relative historyEffect (RxHistory.observePoll pid budget) := by
  intro w h
  let seeded := RxJoint.seed (RxHistory.prior h)
  obtain ⟨suffix,appended⟩ := RxJoint.poll_appends pid budget w seeded
  have actual := RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl appended)
  have seedQuiet : ∀ target, Untouched localEffect seeded target := by
    intro target event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    rfl
  have initial : Tracks localEffect (destinationAt w.wg) seeded w :=
    quiet_append (nil_of_retained localEffect (.refl _)) seedQuiet (.refl _)
  have normal := (poll_tracks (destinationAt w.wg) pid budget w seeded initial).choose_spec.2.2
  rw [actual]
  refine ⟨suffix.map RxHistory.promote,rfl,?_⟩
  cases run : (runPrefix (RxJoint.poll pid budget) w seeded).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    simp only [run] at normal
    change Last localEffect _ _ _ at normal
    rw [appended] at normal
    exact map_last historyEffect RxHistory.promote
      (drop_inert_prefix localEffect seedQuiet normal)

theorem history_poll_tracks (entry : RemoteMap) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Tracks historyEffect entry) (fun _ => True) (RxHistory.observePoll pid budget) :=
  relative_tracks (history_poll_relative pid budget) entry

end Leanux.Proofs.WG.Roaming.RemoteChronology.Poll
