import Leanux.Proofs.WG.Roaming.RemotePollFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemotePoll
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem quiet {E α : Type} (entry : RemoteMap) (cause : E→PeerId→Nat×Nat×Nat×Nat→Prop)
    (g : PrefixM E α) (a : Leanux.M α) (appends : Appends g)
    (erases : ErasesPrefix g a) (keep : ∀initial,Preserves (ProductRetained initial) a) :
    PrefixPreserves (Covered entry cause) (fun _=>True) g := by
  intro w h hi
  obtain ⟨suffix,append⟩:=appends w h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run:(runPrefix g w h).1 with
  | error stop=>trivial
  | ok out=>
    have retained := (hoare_iff_run _ _ _).mp (keep (destinationAt w.wg))
      w out.1 out.2 (RemoteRetained.refl _) ((erases w h).symm.trans run)
    change RemoteCovered entry cause _ _
    rw [append]
    exact (hi.retained retained).append_history

theorem joint_native {α : Type} (entry : RemoteMap) (g : MixedM α) (a : WG.M α)
    (erases : ErasesStatePrefix g a) (keep : ∀initial,Preserves (Retained initial) a) :
    PrefixPreserves (Covered entry localCause) (fun _=>True) (RxJoint.access (liftWGObserver g)) :=
  quiet entry localCause _ _ (RxJoint.access_appends _)
    (RxJoint.access_erases (liftWGObserver_erases erases))
    (fun initial=>PublicationPoll.native_product _ _ (keep initial))

theorem ambient {E α : Type} (entry : RemoteMap) (cause : E→PeerId→Nat×Nat×Nat×Nat→Prop)
    (a : AmbientM α) :
    PrefixPreserves (Covered entry cause) (fun _=>True) (liftPrefix (liftAmbient a)) :=
  quiet entry cause _ _ (Appends.lift _) (erasesPrefix_lift _)
    (fun _=>productAmbient_spec a _ (fun _ _ hi=>hi))

theorem emitted {E : Type} (entry : RemoteMap) (cause : E→PeerId→Nat×Nat×Nat×Nat→Prop) (e : E) :
    PrefixPreserves (Covered entry cause) (fun _=>True) (emitPrefix e) :=
  RxJoint.GroSource.emit_preserves (fun _ _ _=>True.intro) e
    (fun _ _ hi=>hi.append_history)

theorem receipt {E α : Type} (entry : RemoteMap) (cause : E→PeerId→Nat×Nat×Nat×Nat→Prop)
    (a : PrefixM E α) (event : RunWitness α→E)
    (keep : PrefixPreserves (Covered entry cause) (fun _=>True) a) :
    PrefixPreserves (Covered entry cause) (fun _=>True) (receiptObserved a event) :=
  RxJoint.GroSource.receipt_preserves (fun _ _ _=>True.intro) a event keep
    (fun _ _ _ _ _ _ _ hi=>hi.append_history)

theorem capture_covered (entry : RemoteMap) (skb : SkbId) :
    PrefixPreserves (Covered entry localCause) (fun _=>True) (RxJoint.capture skb) := by
  intro w h hi
  obtain ⟨suffix,append⟩:=RxJoint.capture_appends skb w h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run:(runPrefix (RxJoint.capture skb) w h).1 with
  | error stop=>trivial
  | ok out=>
    obtain ⟨⟨pkt,stamp⟩,v⟩:=out
    have same:=(RxDisposition.capture_selected skb w v h pkt stamp run).1
    change RemoteCovered entry localCause _ _
    rw [same,append]
    exact hi.append_history

theorem consume_covered (entry : RemoteMap) (pid occurrence id : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (Covered entry localCause) (fun _=>True)
      (RxJoint.consume pid occurrence id stamp pkt ep) := by
  intro w h hi
  obtain ⟨suffix,append⟩:=RxJoint.access_appends
    (liftWGObserver (consumeDataDonePrefix pid pkt ep)) w h
  rw [RxJoint.consume_run]
  cases run:runPrefix (RxJoint.access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t=>
    simp only [run] at append
    cases result with
    | error stop=>exact ⟨suffix,append,True.intro,True.intro⟩
    | ok out=>
      obtain ⟨returned,v⟩:=out
      have native := (RxJoint.access_erases (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h).symm.trans (congrArg Prod.fst run)
      rw [liftWG_run] at native
      cases original:((consumeDataDone pid pkt ep).run w.wg).run w.ambient with
      | error stop=>simp [original,Except.map] at native
      | ok out=>
        obtain ⟨⟨value,g⟩,after⟩:=out
        simp only [original,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
        obtain ⟨rfl,rfl⟩:=native
        let r : RxDisposition.ConsumeReceipt := ⟨pid,pkt,ep,⟨value,w.wg,g,w.ambient,after⟩⟩
        have effect:=RemoteControl.consumeDataDone_all_remotes (destinationAt w.wg) pid pkt ep
          w.wg w.ambient value g after rfl original
        have next : Covered entry localCause (t++[.consumed occurrence id stamp r]) {w with wg:=g,ambient:=after} := by
          change RemoteCovered entry localCause _ _
          rw [append]
          apply hi.append_history.receipt
          intro other remote present
          by_cases valid:ep.family=AF_INET ∨ ep.family=AF_INET6
          · simp only [RemoteControl.setterRemotes,ite_eq_left valid] at effect
            by_cases same:other=pid
            · subst other
              exact Or.inr ⟨rfl,(effect.updated_selected present).symm,valid⟩
            · exact Or.inl (effect.updated_other same present)
          · simp only [RemoteControl.setterRemotes,ite_eq_right valid] at effect
            exact Or.inl (effect other remote present)
        cases value with
        | none=>exact ⟨suffix++[_],by simp only [append,List.append_assoc]; rfl,True.intro,next⟩
        | some bytes=>
          exact ⟨suffix++[_,_],by simp only [append,List.append_assoc]; rfl,True.intro,next.append_history⟩

theorem gro_receive_covered (entry : RemoteMap) (g : RxJoint.Gro) (e : RxJoint.Entry) :
    PrefixPreserves (Covered entry localCause) (fun _=>True) (RxJoint.receive g e) := by
  rw [RxJoint.GroSource.receive_factor]
  apply RxJoint.GroSource.receive_preserves id _ (fun _ _ _=>True.intro)
  · intro e h w hi; exact hi.append_history
  · intro bytes
    exact quiet entry localCause _ _ (RxJoint.access_appends _)
      (RxJoint.access_erases (stackReceivePrefix_erases bytes)) (fun initial=>stack_retained initial bytes)
  · intro e w h x v t _ _ hi; exact hi.append_history

theorem gro_flush_covered (entry : RemoteMap) (g : RxJoint.Gro) :
    PrefixPreserves (Covered entry localCause) (fun _=>True) (RxJoint.flushAll g) := by
  rw [RxJoint.GroSource.flushAll_factor]
  apply RxJoint.GroSource.flushAll_preserves id _ (fun _ _ _=>True.intro)
  · intro e h w hi; exact hi.append_history
  · intro bytes
    exact quiet entry localCause _ _ (RxJoint.access_appends _)
      (RxJoint.access_erases (stackReceivePrefix_erases bytes)) (fun initial=>stack_retained initial bytes)
  · intro e w h x v t _ _ hi; exact hi.append_history

theorem poll_covered (entry : RemoteMap) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Covered entry localCause) (fun _=>True) (RxJoint.poll pid budget) := by
  rw [RxJoint.PollSource.poll_factor]
  apply RxJoint.PollSource.poll_preserves (fun {_} a=>a) _ _ (fun _ _ _=>True.intro)
  · intro peer; exact joint_native entry _ _ (RxJoint.peekAccess_erases peer)
      (fun initial=>(peek_frame peer).wp (RemoteRetained initial))
  · intro first; exact joint_native entry _ _ (RxJoint.readyAccess_erases first)
      (fun initial=>ready_retained initial first)
  · exact capture_covered entry
  · intro peer n skb stamp
    unfold RxJoint.drop
    exact (joint_native entry _ _ (rxDropPeekedPrefix_erases peer)
      (fun initial=>(drop_frame peer).wp (RemoteRetained initial))).bind
        (fun _=>emitted entry localCause _)
  · intro n skb stamp pkt
    exact receipt entry localCause _ _ (ambient entry localCause (AmbientM.branch .rxPollNotCrypted (pkt.state != .crypted)))
  · intro n skb stamp pkt
    exact receipt entry localCause _ _ (joint_native entry _ _ (counterValidatePrefix_erases pkt.keypair pkt.nonce)
      (fun initial=>counter_retained initial pkt.keypair pkt.nonce))
  · intro n skb stamp pkt
    exact receipt entry localCause _ _ (quiet entry localCause _ _ (Appends.lift _) (erasesPrefix_lift _)
      (fun initial=>PublicationPoll.native_product _ _
        ((RemoteCompletion.store_remotes (endpointFromSkb_sameWGStore pkt.source)).wp (RemoteRetained initial))))
  · exact consume_covered entry
  · intro kid; exact joint_native entry _ _ (keypairPutPrefix_erases (some kid) false)
      (fun initial=>keypairPut_retained initial (some kid) false)
  · intro peer; exact joint_native entry _ _ (peerPutMixed_erases (some peer))
      (fun initial=>(ensures_iff _ _ _).mp (peerPut_remotes (some peer) initial))
  · intro skb; exact joint_native entry _ _ (freeRxSkbPrefix_erases skb)
      (fun initial=>(packet_frame (SkbStore.freeRx skb)).wp (RemoteRetained initial))
  · intro peer; exact joint_native entry _ _ (RxJoint.completeAccess_erases peer)
      (fun initial=>(complete_frame peer).wp (RemoteRetained initial))
  · intro b; exact ambient entry localCause (AmbientM.branch .rxPollNoBudget b)
  · intro b; exact ambient entry localCause (AmbientM.branch .rxPollCounterInvalid b)
  · intro b; exact ambient entry localCause (AmbientM.branch .rxPollEndpointFailed b)
  · intro b; exact ambient entry localCause (AmbientM.branch .rxPollFree b)
  · intro b; exact ambient entry localCause (AmbientM.branch .rxPollBudgetDone b)
  · intro b; exact ambient entry localCause (AmbientM.branch .rxPollComplete b)
  · exact gro_receive_covered entry
  · exact gro_flush_covered entry

end Leanux.Proofs.WG.Roaming.RemotePoll
