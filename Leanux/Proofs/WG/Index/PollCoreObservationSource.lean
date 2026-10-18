import Leanux.Proofs.WG.Index.PollCoreReleaseSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.PollCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem observed {E α : Type} (P : World→Prop) (g : PrefixM E α) (action : Leanux.M α)
    (appends : Appends g) (erase : ErasesPrefix g action) (keep : Preserves P action) :
    PrefixPreserves (fun _=>P) (fun _=>True) g := by
  intro w h pre
  obtain ⟨suffix,append⟩ := appends w h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error stop=>trivial
  | ok out=>exact (hoare_iff_run _ _ _).mp keep w out.1 out.2 pre ((erase w h).symm.trans run)

theorem original {E α : Type} (P : World→Prop) (g : PrefixM E α) (action : Leanux.M α)
    (erase : ErasesPrefix g action)
    (keep : PrefixPreserves (fun _=>P) (fun _=>True) g) : Preserves P action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v pre run
  have final := (keep w [] pre).choose_spec.2.2
  simpa only [(erase w []).trans run] using final

theorem native_observed {α : Type} (P : WGWorld→Prop) (g : MixedM α) (action : WG.M α)
    (erase : ErasesStatePrefix g action) (keep : Preserves P action) :
    PrefixPreserves (fun _ w=>P w.wg) (fun _=>True) (RxJoint.access (liftWGObserver g)) :=
  observed _ _ _ (RxJoint.access_appends _)
    (RxJoint.access_erases (liftWGObserver_erases erase)) (PublicationPoll.native_product _ _ keep)

theorem lifted {E α : Type} (P : World→Prop) (action : Leanux.M α) (keep : Preserves P action) :
    PrefixPreserves (fun (_ : List E)=>P) (fun _=>True) (liftPrefix action) :=
  PrefixEnsures.lift action (fun _ _ _=>True.intro)
    (fun _ w x v pre run=>(hoare_iff_run _ _ _).mp keep w x v pre run)

theorem ambient {E α : Type} (P : WGWorld→Prop) (action : AmbientM α) :
    PrefixPreserves (fun (_ : List E) w=>P w.wg) (fun _=>True) (liftPrefix (liftAmbient action)) :=
  lifted (fun w=>P w.wg) _ (productAmbient_spec action (fun w=>P w.wg) (fun _ _ pre=>pre))

theorem emitted {E : Type} (P : World→Prop) (event : E) :
    PrefixPreserves (fun _=>P) (fun _=>True) (emitPrefix event) :=
  RxJoint.GroSource.emit_preserves (fun _ _ _=>True.intro) event (fun _ _ pre=>pre)

theorem receipt {α : Type} (P : World→Prop) (action : RxJoint.Obs α)
    (event : RunWitness α→RxJoint.Event)
    (keep : PrefixPreserves (fun _=>P) (fun _=>True) action) :
    PrefixPreserves (fun _=>P) (fun _=>True) (receiptObserved action event) :=
  RxJoint.GroSource.receipt_preserves (fun _ _ _=>True.intro) _ _ keep
    (fun _ _ _ _ _ _ _ pre=>pre)

theorem capture (P : World→Prop) (skb : SkbId) :
    PrefixPreserves (fun _=>P) (fun _=>True) (RxJoint.capture skb) := by
  intro w h pre
  obtain ⟨suffix,append⟩ := RxJoint.capture_appends skb w h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run:(runPrefix (RxJoint.capture skb) w h).1 with
  | error stop=>trivial
  | ok out=>
    rcases out with ⟨⟨pkt,stamp⟩,v⟩
    exact (RxDisposition.capture_selected skb w v h pkt stamp run).1 ▸ pre

theorem consume_loop (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (fun _ w=>Loop pid w.wg) (fun _=>True) (RxJoint.consume pid n skb stamp pkt ep) := by
  intro w h pre
  obtain ⟨suffix,append⟩ := RxJoint.consume_appends pid n skb stamp pkt ep w h
  refine ⟨suffix,append,True.intro,?_⟩
  have keep := native_observed (Loop pid) _ _ (consumeDataDonePrefix_erases pid pkt ep)
    (native_loop pid _ (ReceiveCompletion.consume_ready pid pkt ep)
      (fun entry=>DriverTags.Silent.consumeDataDone_retained entry pid pkt ep)) w h pre
  rw [RxJoint.consume_run]
  cases run:runPrefix (RxJoint.access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t=>
    have normal := keep.choose_spec.2.2
    simp only [run] at normal
    cases result with
    | error stop=>trivial
    | ok result=>
      rcases result with ⟨out,v⟩
      cases out <;> exact normal

theorem stack_loop (pid : PeerId) (bytes : List UInt8) :
    Preserves (fun w : World=>Loop pid w.wg) (Env.deliverInner bytes) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  rcases pre with ready|absent
  · exact Or.inl ((hoare_iff_run _ _ _).mp (TransmitCore.stack_ready bytes) w result v ready run)
  · right
    exact absent_retained ((hoare_iff_run _ _ _).mp
      (DriverTags.Stack.native (responseTagMap w.wg.dev) bytes)
        w result v (TagsRetained.refl _) run) absent

theorem gro_receive (P : World→Prop)
    (stack : ∀bytes,Preserves P (Env.deliverInner bytes)) (g : RxJoint.Gro) (e : RxJoint.Entry) :
    PrefixPreserves (fun _=>P) (fun _=>True) (RxJoint.receive g e) := by
  rw [RxJoint.GroSource.receive_factor]
  apply RxJoint.GroSource.receive_preserves id _ (fun _ _ _=>True.intro)
  · intro _ _ _ pre; exact pre
  · intro bytes
    exact observed P _ _ (RxJoint.access_appends _)
      (RxJoint.access_erases (stackReceivePrefix_erases bytes)) (stack bytes)
  · intro _ _ _ _ _ _ _ _ pre; exact pre

theorem gro_flush (P : World→Prop)
    (stack : ∀bytes,Preserves P (Env.deliverInner bytes)) (g : RxJoint.Gro) :
    PrefixPreserves (fun _=>P) (fun _=>True) (RxJoint.flushAll g) := by
  rw [RxJoint.GroSource.flushAll_factor]
  apply RxJoint.GroSource.flushAll_preserves id _ (fun _ _ _=>True.intro)
  · intro _ _ _ pre; exact pre
  · intro bytes
    exact observed P _ _ (RxJoint.access_appends _)
      (RxJoint.access_erases (stackReceivePrefix_erases bytes)) (stack bytes)
  · intro _ _ _ _ _ _ _ _ pre; exact pre

theorem complete_observed (pid : PeerId) :
    PrefixEnsures (fun _ w=>Loop pid w.wg) (fun _=>True)
      (RxJoint.access (liftWGObserver (RxJoint.completeAccess pid)))
      (fun _ _ w=>TimerCore.Ready w.wg) := by
  intro w h pre
  obtain ⟨suffix,append⟩ := RxJoint.access_appends (liftWGObserver (RxJoint.completeAccess pid)) w h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run:(runPrefix (RxJoint.access (liftWGObserver (RxJoint.completeAccess pid))) w h).1 with
  | error stop=>trivial
  | ok out=>
    have actual := (RxJoint.access_erases (liftWGObserver_erases (RxJoint.completeAccess_erases pid)) w h).symm.trans run
    have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
      _ w out.2 out.1 actual
    exact (hoare_iff_run_ambient _ _ _).mp (complete_exit pid)
      w.wg w.ambient out.1 out.2.wg out.2.ambient pre native

end Leanux.Proofs.WG.Index.PollCore
