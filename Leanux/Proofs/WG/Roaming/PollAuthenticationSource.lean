import Leanux.Proofs.WG.Roaming.PollAuthenticationSelectionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes RxJoint

theorem state_snoc (history : List RxHistory.Event) (h : List Event) (w : World)
    (e : Event) (hi : State history h w) (facts : EventFacts history e) :
    State history (h++[e]) w :=
  ⟨hi.1,checks_append hi.2 (by intro x member; cases List.mem_singleton.mp member; exact facts)⟩

theorem emitted (history : List RxHistory.Event) (e : Event)
    (facts : EventFacts history e) :
    PrefixPreserves (State history) (Checks history) (emitPrefix e) :=
  GroSource.emit_preserves (fun _ _ hi=>hi.2) e
    (fun h w hi=>state_snoc history h w e hi facts)

theorem consumed (history : List RxHistory.Event) (pid n id : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (State history) (Checks history) (consume pid n id stamp pkt ep) := by
  unfold consume
  apply PrefixPreserves.bind
    (native_access history _ _ (consumeDataDonePrefix_erases pid pkt ep)
      (PublicationCompletion.consumeDataDone_preserves pid pkt ep history)).captureObserved
  intro r
  apply PrefixPreserves.bind (emitted history
    (.consumed n id stamp ⟨pid,pkt,ep,⟨r.value,r.before.wg,r.after.wg,r.before.ambient,r.after.ambient⟩⟩)
    True.intro)
  intro _
  cases r.value with
  | none => exact PrefixPreserves.pure (fun _ _ hi=>hi.2) _
  | some bytes =>
    exact (emitted history
      (.buffered ⟨⟨n,id,bytes⟩,stamp,some ⟨pid,pkt,ep,⟨some bytes,r.before.wg,r.after.wg,r.before.ambient,r.after.ambient⟩⟩⟩)
      True.intro).bind
      (fun _=>PrefixPreserves.pure (fun _ _ hi=>hi.2) _)

theorem counter_block (history : List RxHistory.Event) (pid n id : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (crypted : pkt.state=.crypted) :
    PrefixEnsures (Selected history id stamp pkt) (Checks history)
      (Noise.CounterConsume.counterBlock pid n id stamp pkt) (fun _=>State history) := by
  have statePure {α : Type} (x : α) : PrefixEnsures (State history) (Checks history)
      (pure x) (fun _=>State history) :=
    PrefixEnsures.pure (fun _ _ hi=>hi.2) (fun _ _ hi=>hi)
  have selectedPure {α : Type} (x : α) : PrefixEnsures (Selected history id stamp pkt)
      (Checks history) (pure x) (fun _=>State history) :=
    PrefixEnsures.pure (fun _ _ hi=>hi.1.2) (fun _ _ hi=>hi.1)
  unfold Noise.CounterConsume.counterBlock
  apply PrefixEnsures.bind (selected_counter history n id stamp pkt)
  intro b
  dsimp only
  apply PrefixEnsures.bind (Q:=fun _=>Selected history id stamp pkt) (selected_ambient history id stamp pkt .rxPollCounterInvalid (!b))
  intro rejected
  split
  · apply PrefixEnsures.bind (endpoint history n id stamp pkt crypted)
    intro ep
    apply PrefixEnsures.bind (Q:=fun _=>State history) (lifted history (branch .rxPollEndpointFailed ep.isNone)
      (productAmbient_spec (AmbientM.branch .rxPollEndpointFailed ep.isNone) _ (fun _ _ hi=>hi)))
    intro failed
    split
    · cases ep with
      | none =>
        intro w h hi
        exact ⟨[],by change h=h++[];simp,hi.2,True.intro⟩
      | some ep =>
        exact PrefixEnsures.bind (consumed history pid n id stamp pkt ep)
          (fun _=>statePure _)
    · exact statePure _
  · exact selectedPure _

theorem stack (history : List RxHistory.Event) (bytes : List UInt8) :
    PrefixPreserves (State history) (Checks history) (access (stackReceivePrefix bytes)) :=
  keep history _ (Env.deliverInner bytes) (checks_access history _)
    (access_erases (stackReceivePrefix_erases bytes))
    (PublicationStack.deliverInner_preserves bytes history)

theorem received (history : List RxHistory.Event) (g : Gro) (e : Entry) :
    PrefixPreserves (State history) (Checks history) (receive g e) := by
  rw [GroSource.receive_factor]
  apply GroSource.receive_preserves _root_.id _ (fun _ _ hi=>hi.2)
  · intro e h w hi; exact state_snoc history h w (.entered e) hi True.intro
  · exact stack history
  · intro e w h x v t hi run next
    exact state_snoc history t v (.completed e ⟨x,w,v⟩) next True.intro

theorem flushed (history : List RxHistory.Event) (g : Gro) :
    PrefixPreserves (State history) (Checks history) (flushAll g) := by
  rw [GroSource.flushAll_factor]
  apply GroSource.flushAll_preserves _root_.id _ (fun _ _ hi=>hi.2)
  · intro e h w hi; exact state_snoc history h w (.entered e) hi True.intro
  · exact stack history
  · intro e w h x v t hi run next
    exact state_snoc history t v (.completed e ⟨x,w,v⟩) next True.intro

theorem poll (history : List RxHistory.Event) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (State history) (Checks history) (RxJoint.poll pid budget) := by
  apply Noise.CounterConsume.poll_preserves_selected
    (State history) (Checks history) (Selected history)
    (fun _ _ hi=>hi.2) (fun _ _ _ _ _ hi=>hi.1)
  · intro p; exact native_access history _ _ (peekAccess_erases p)
      (PublicationPoll.peek_preserves p history)
  · intro first
    apply native_access history _ _ (readyAccess_erases first)
    unfold WG.andM branch invariant
    repeat' publication_poll_native history
  · exact captured history
  · exact dropped history
  · exact selected_state history
  · exact counter_block history
  · intro id; exact native_access history _ _ (keypairPutPrefix_erases _ _)
      (PublicationPoll.keypairPut_preserves _ _ history)
  · intro p; exact native_access history _ _ (peerPutMixed_erases _)
      (PublicationPoll.peerPut_preserves _ history)
  · intro id; exact native_access history _ _ (freeRxSkbPrefix_erases _)
      (PublicationHistory.freeRxSkb_preserves _ history)
  · intro p; exact native_access history _ _ (completeAccess_erases p)
      (PublicationPoll.complete_preserves p history)
  · intro site b; exact lifted history _
      (productAmbient_spec (AmbientM.branch site b) _ (fun _ _ hi=>hi))
  · exact received history
  · exact flushed history

theorem poll_seed (history : List RxHistory.Event) (pid : PeerId) (budget : Nat)
    (w : World) (prior : List LifetimeEvent)
    (hi : PublicationHistory.Inv history w.wg) :
    Checks history (runPrefix (RxJoint.poll pid budget) w (seed prior)).2 := by
  apply (poll history pid budget w (seed prior) _).choose_spec.2.1
  refine ⟨hi,?_⟩
  intro e member
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp member
  trivial

end Leanux.Proofs.WG.Roaming.PollAuthentication
