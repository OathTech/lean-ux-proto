import Leanux.Proofs.WG.Queues.RxTransmitChecks
import Leanux.Proofs.WG.Queues.GroPreservation
import Leanux.Proofs.WG.Queues.PollPreservation
import Leanux.Proofs.WG.Configuration.RoutingPoll

/-! Actual local Stack/GRO and poll composition for positional transmit
checks. The old atoms retain their original RX journal, while only the native
transmit callback can emit a local handoff receipt. -/
namespace Leanux.Proofs.WG.Queues.RxTransmit.Position
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Packets AllowedIps RxJoint

theorem Inv.store (h : List LocalEvent) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : Inv initial prior h w) :
    Inv initial prior h v := by
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  exact ⟨by simpa only [GlobalCompletionState,routingView,device] using hi.1,hi.2⟩

theorem Inv.productStore (h : List LocalEvent) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : Inv initial prior h w) :
    Inv initial prior h v :=
  hi.store h w v (congrArg (fun s : ProductStore43 => s.2.2.2) same)

theorem quiet_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (g : PrefixM LocalEvent α) (appends : Appends g) (quiet : HistoryFrame receiptEvent g)
    (routing : ∀ w h x v, GlobalCompletionState initial (TransmitJoint.routes prior) w.wg →
      (runPrefix g w h).1 = .ok (x,v) →
      GlobalCompletionState initial (TransmitJoint.routes prior) v.wg) :
    PrefixPreserves (Inv initial prior) (Safe initial prior) g := by
  intro w h hi
  obtain ⟨suffix,append⟩ := appends w h
  have checked : Checks initial prior (runPrefix g w h).2 := by
    intro r member
    exact hi.2 r (quiet w h ▸ member)
  refine ⟨suffix,append,⟨hi.1.1,checked⟩,?_⟩
  cases run : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out => exact ⟨routing w h out.1 out.2 hi.1 run,checked⟩

theorem old_normal (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (g : RxJoint.Obs α)
    (routing : ∀ w h x v, GlobalCompletionState initial (TransmitJoint.routes prior) w.wg →
      (runPrefix g w h).1 = .ok (x,v) →
      GlobalCompletionState initial (TransmitJoint.routes prior) v.wg) :
    PrefixPreserves (Inv initial prior) (Safe initial prior)
      (focusPrefix LocalEvent.old oldRx g) :=
  quiet_preserves initial prior _ (Appends.focus _ _ _)
    (focusPrefix_other _ _ _ (fun _ => rfl) g)
    (fun w h x v hi run => routing w (h.filterMap oldRx) x v hi run)

theorem old_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (g : RxJoint.Obs α) (a : Leanux.M α) (erase : ErasesPrefix g a)
    (routing : ProductRetainsRoutingCall a) :
    PrefixPreserves (Inv initial prior) (Safe initial prior)
      (focusPrefix LocalEvent.old oldRx g) := by
  apply old_normal initial prior g
  intro w h x v hi run
  exact ⟨hi.1,hi.2.retains ((ProjectedAction.iff_run _ _ _).mp routing w x v
    ((erase w h).symm.trans run))⟩

theorem native_old_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (g : MixedM α) (a : WG.M α) (erase : ErasesStatePrefix g a)
    (routing : RetainsRoutingCall a) :
    PrefixPreserves (Inv initial prior) (Safe initial prior)
      (focusPrefix LocalEvent.old oldRx (access (liftWGObserver g))) :=
  old_preserves initial prior _ _ (access_erases (liftWGObserver_erases erase)) routing.liftWG

theorem ambient_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (a : AmbientM α) :
    PrefixPreserves (Inv initial prior) (Safe initial prior) (liftPrefix (liftAmbient a)) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.safe) Inv.productStore
    (fun state => productAmbient_spec a (fun w => productStoreView w = state) (fun _ _ hi => hi))

theorem stack_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (packet : List UInt8) :
    PrefixPreserves (Inv initial prior) (Safe initial prior)
      (stackReceiveWith (receive4With (reply4With transmit)) packet) :=
  stackReceiveWith_preserves (fun _ _ hi => hi.safe) Inv.productStore _
    (fun bytes => receive4With_preserves (fun _ _ hi => hi.safe) Inv.productStore _
      (fun dst reply => reply4With_preserves (fun _ _ hi => hi.safe) Inv.productStore
        transmit (transmit_preserves initial prior) dst reply) bytes) packet

theorem gro_receive_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (g : Gro) (e : RxJoint.Entry) :
    PrefixPreserves (Inv initial prior) (Safe initial prior)
      (GroSource.receiveWith LocalEvent.old (stackReceiveWith (receive4With (reply4With transmit))) g e) := by
  apply GroSource.receive_preserves LocalEvent.old _ (fun _ _ hi => hi.safe)
  · intro e h w hi
    exact ⟨hi.1,by simpa only [Checks,List.filterMap_append,List.filterMap_cons,
      receiptEvent,List.filterMap_nil,List.append_nil] using hi.2⟩
  · exact stack_preserves initial prior
  · intro e w h x v t _ _ hi
    exact ⟨hi.1,by simpa only [Checks,List.filterMap_append,List.filterMap_cons,
      receiptEvent,List.filterMap_nil,List.append_nil] using hi.2⟩

theorem gro_flush_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (g : Gro) :
    PrefixPreserves (Inv initial prior) (Safe initial prior)
      (GroSource.flushAllWith LocalEvent.old (stackReceiveWith (receive4With (reply4With transmit))) g) := by
  apply GroSource.flushAll_preserves LocalEvent.old _ (fun _ _ hi => hi.safe)
  · intro e h w hi
    exact ⟨hi.1,by simpa only [Checks,List.filterMap_append,List.filterMap_cons,
      receiptEvent,List.filterMap_nil,List.append_nil] using hi.2⟩
  · exact stack_preserves initial prior
  · intro e w h x v t _ _ hi
    exact ⟨hi.1,by simpa only [Checks,List.filterMap_append,List.filterMap_cons,
      receiptEvent,List.filterMap_nil,List.append_nil] using hi.2⟩

private theorem capture_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (skb : SkbId) :
    PrefixPreserves (Inv initial prior) (Safe initial prior)
      (focusPrefix LocalEvent.old oldRx (capture skb)) := by
  apply old_normal initial prior _
  intro w h x v hi run
  obtain ⟨rfl,_⟩ := RxDisposition.capture_selected skb w v h x.1 x.2 run
  exact hi

private theorem consume_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (Inv initial prior) (Safe initial prior)
      (focusPrefix LocalEvent.old oldRx (consume pid n skb stamp pkt ep)) := by
  apply old_normal initial prior _
  intro w h x v hi run
  have projection := congrArg Prod.fst (consume_gro pid n skb stamp pkt ep w h)
  have erased := consumeGro_erases pid n skb pkt ep w (h.filterMap groEvent)
  rw [projection,run] at erased
  have source : (liftWG (consumeDataDone pid pkt ep)).run w =
      .ok ((x.map Entry.tag).map GroEntry.bytes,v) := erased.symm
  exact ⟨hi.1,hi.2.retains ((ProjectedAction.iff_run _ _ _).mp
    (consumeDataDone_routing pid pkt ep).liftWG w _ v source)⟩

theorem poll_preserves (initial : FlatTable × FlatTable) (prior : List TransmitJoint.Event)
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Inv initial prior) (Safe initial prior)
      (PollSource.pollWith (fun {_} g => focusPrefix LocalEvent.old oldRx g)
        (GroSource.receiveWith LocalEvent.old (stackReceiveWith (receive4With (reply4With transmit))))
        (GroSource.flushAllWith LocalEvent.old (stackReceiveWith (receive4With (reply4With transmit))))
        pid budget) := by
  have packets {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
    intro value
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa only [routingView,hd,Option.map_some,routingState] using hi
  have ambient {α : Type} (a : AmbientM α) : ProductRetainsRoutingCall (liftAmbient a) :=
    ProjectedRetainsRoutingCall.of_same (fun value =>
      productAmbient_spec a (fun w => routingView w.wg = value) (fun _ _ hi => hi))
  apply PollSource.poll_preserves _ _ _ (fun _ _ hi => hi.safe)
  · intro peer
    exact native_old_preserves initial prior _ _ (peekAccess_erases peer)
      (ProjectedRetainsRoutingCall.of_same
        ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingRxFrames.«0».Leanux.Proofs.WG.AllowedIps.peekRxQueue_routing) peer))
  · intro first
    apply native_old_preserves initial prior _ _ (readyAccess_erases first)
    apply ProjectedRetainsRoutingCall.of_same
    routing_handshake_source [WG.andM,getRxSkb] using [packets]
  · exact capture_preserves initial prior
  · intro peer n skb stamp
    apply old_normal initial prior _
    intro w h x v hi run
    have erased := access_erases (liftWGObserver_erases (rxDropPeekedPrefix_erases peer)) w h
    rw [drop,runPrefix_bind] at run
    cases lower : runPrefix (access (liftWGObserver (rxDropPeekedPrefix peer))) w h with
    | mk result hist =>
      rw [lower] at run erased
      cases result with
      | error stop => cases run
      | ok out =>
        rcases out with ⟨value,u⟩
        change Except.ok ((),u) = Except.ok (x,v) at run
        cases run
        exact ⟨hi.1,hi.2.retains ((ProjectedAction.iff_run _ _ _).mp
          (RetainsRoutingCall.liftWG (ProjectedRetainsRoutingCall.of_same
            ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingRxFrames.«0».Leanux.Proofs.WG.AllowedIps.dropRxQueue_routing) peer)))
          w value v erased.symm)⟩
  · intro n skb stamp pkt
    exact old_preserves initial prior _ _ (RxLink.receipt_erases (erasesPrefix_lift _))
      (ambient (AmbientM.branch .rxPollNotCrypted (pkt.state != .crypted)))
  · intro n skb stamp pkt
    exact old_preserves initial prior _ _
      (RxLink.receipt_erases (access_erases (liftWGObserver_erases
        (counterValidatePrefix_erases pkt.keypair pkt.nonce))))
      (RetainsRoutingCall.liftWG (ProjectedRetainsRoutingCall.of_same (counterValidate_routing pkt.keypair pkt.nonce)))
  · intro n skb stamp pkt
    exact old_preserves initial prior _ _ (RxLink.receipt_erases (erasesPrefix_lift _))
      (RetainsRoutingCall.liftWG (ProjectedRetainsRoutingCall.of_same (routing_kernel _ (endpointFromSkb_sameWGStore pkt.source))))
  · exact consume_preserves initial prior
  · intro key
    exact native_old_preserves initial prior _ _ (keypairPutPrefix_erases (some key) false)
      (ProjectedRetainsRoutingCall.of_same (keypairPut_routing (some key) false))
  · intro peer
    exact native_old_preserves initial prior _ _ (peerPutMixed_erases (some peer))
      (peerPut_retainsRouting (some peer))
  · intro skb
    exact native_old_preserves initial prior _ _ (freeRxSkbPrefix_erases skb)
      (ProjectedRetainsRoutingCall.of_same (packets (SkbStore.freeRx skb)))
  · intro peer
    exact native_old_preserves initial prior _ _ (completeAccess_erases peer)
      (ProjectedRetainsRoutingCall.of_same
        ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingRxFrames.«0».Leanux.Proofs.WG.AllowedIps.completeRxQueue_routing) peer))
  · intro b; exact ambient_preserves initial prior (AmbientM.branch .rxPollNoBudget b)
  · intro b; exact ambient_preserves initial prior (AmbientM.branch .rxPollCounterInvalid b)
  · intro b; exact ambient_preserves initial prior (AmbientM.branch .rxPollEndpointFailed b)
  · intro b; exact ambient_preserves initial prior (AmbientM.branch .rxPollFree b)
  · intro b; exact ambient_preserves initial prior (AmbientM.branch .rxPollBudgetDone b)
  · intro b; exact ambient_preserves initial prior (AmbientM.branch .rxPollComplete b)
  · exact gro_receive_preserves initial prior
  · exact gro_flush_preserves initial prior

theorem observed_preserves (initial : FlatTable × FlatTable) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (TransmitJoint.Inv initial) (TransmitJoint.Safe initial)
      (RxHistory.ObserveSource.seededWith seed promote
        (PollSource.pollWith (fun {_} g => focusPrefix LocalEvent.old oldRx g)
          (GroSource.receiveWith LocalEvent.old (stackReceiveWith (receive4With (reply4With transmit))))
          (GroSource.flushAllWith LocalEvent.old (stackReceiveWith (receive4With (reply4With transmit))))
          pid budget)) :=
  seeded_preserves initial _ (fun prior => poll_preserves initial prior pid budget)

end Leanux.Proofs.WG.Queues.RxTransmit.Position
