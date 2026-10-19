import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverStaging
import Leanux.Proofs.WG.RetirementSecurity.RxPollOccurrenceFrames

/-! Receive-triggered staging and actual indexed NAPI bookkeeping preserve
TX allocation origins. The RX authentication argument remains independent. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def ProductInv (h : List Journal.Event) (w : World) : Prop := JournalInv h w.wg
abbrev ProductSafe (g : PrefixM Journal.Event α) := PrefixPreserves ProductInv Safe g

theorem product_state {g : WGPrefix Journal.Event α} (safe : StateSafe g) : ProductSafe (liftWGObserver g) :=
  safe.liftWGObserver

theorem product_pure (x : α) : ProductSafe (pure x) := PrefixPreserves.pure (fun _ _ hi => hi.2) x

theorem product_loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → PrefixM Journal.Event (ForInStep β)) (safe : ∀ x b, ProductSafe (g x b)) :
    ProductSafe (forIn xs b g) :=
  PrefixEnsures.forInInvariant xs b g (fun _ h w => ProductInv h w) Safe (fun _ _ _ hi => hi.2) safe

theorem product_quiet {g : PrefixM Journal.Event α} {action : Leanux.M α}
    (app : Appends g) (quiet : HistoryFrame watched? g)
    (erase : ErasesPrefix g action)
    (native : ∀ h, Preserves (fun w : World => Inv h w.wg) action) : ProductSafe g := by
  intro w h hi
  obtain ⟨suffix,eq⟩ := app w h
  have noCipher : suffix.filterMap watched? = [] := by
    have same := quiet w h
    rw [eq,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap watched? with
    | nil => rfl
    | cons e es =>
      simp only [List.length_append,found,List.length_cons] at lengths
      omega
  have safe : Safe (runPrefix g w h).2 := by rw [eq]; exact hi.2.quiet_suffix noCipher
  refine ⟨suffix,eq,safe,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok value =>
    have kept := (hoare_iff_run _ _ _).mp (native h) w value.1 value.2 hi.1 ((erase w h).symm.trans result)
    refine ⟨kept.mono ?_,safe⟩
    intro e member
    rw [eq]
    exact List.mem_append_left _ member

theorem confirmation (pid : PeerId) (kid : KeypairId) : StateSafe (Journal.confirmation pid kid) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl)
      ((HandshakeSecurity.Responder.DriverCuts.confirmation pid kid).run w))
    (focusStatePrefix_erases _ _ (HandshakeSecurity.Responder.DriverCuts.confirmation_erases pid kid))
    (fun _ => frame (snapshot_wire (confirmation_cryptWire pid kid)))

theorem counter (skb : SkbId) (pkt : RxPacket) :
    ProductSafe (AuthenticatedEffects.TransportDriver.counter Journal.Event.replay skb pkt) :=
  product_quiet (Appends.lift _).receiptObserved
    (HistoryFrame.receiptObserved (HistoryFrame.lift _ _) (fun _ => rfl))
    (AuthenticatedEffects.TransportDriver.counter_erases _ _ _)
    (fun _ => PublicationPoll.native_product _ _ (frame (snapshot_wire (RxPollOccurrences.counter_wire pkt.keypair pkt.nonce))))

theorem receive_tail (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StateSafe (Driver.receiveTailObserved Journal.hooks pid pkt confirmed) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold Driver.receiveTailObserved
  simp only [Driver.nested_prepare_lift Journal.hooks rfl rfl,Driver.rxFinish_lift Journal.hooks rfl]
  repeat' first
    | (nonce_source_head Driver.stagingObserved; exact staging _)
    | (nonce_source_head timersHandshakeComplete; exact state_lift _ (fun _ => frame (snapshot_wire (handshakeComplete_cryptWire _ _))))
    | (nonce_source_head RxCredits.prepareRest; exact state_lift _ (fun _ => frame (snapshot_wire (prepareRest_cryptWire _ _))))
    | (nonce_source_head Packets.rxFinish; exact state_lift _ (fun _ => frame (snapshot_wire (finishRx_cryptWire _ _))))
    | origin_driver_step

theorem consume (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StateSafe (Driver.consumeObserved Journal.hooks pid pkt ep) := by
  unfold Driver.consumeObserved
  dsimp only [Journal.hooks]
  apply StatePrefixEnsures.bind (state_lift _ (fun _ => frame (snapshot_wire (endpoint_cryptWire pid ep))))
  intro _
  apply StatePrefixEnsures.bind (confirmation pid pkt.keypair)
  intro confirmed
  exact receive_tail pid pkt confirmed

macro "origin_poll_frame" : tactic => `(tactic| first
  | (rx_retention_head PrevQueue.peek; exact NativeFrames.store (prevQueuePeek_sameWGStore _))
  | (rx_retention_head endpointFromSkb; exact NativeFrames.store (endpointFromSkb_sameWGStore _))
  | (rx_retention_head getRxSkb; exact frame (snapshot_wire (ReceiveOccurrences.get_rx_wire _)))
  | (rx_retention_head freeRxSkb; exact frame (snapshot_wire (ReceiveOccurrences.free_rx_wire _)))
  | (rx_retention_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | origin_staging_frame)

theorem poll (pid : PeerId) (budget : Nat) (callback : List (List UInt8) → PrefixM Journal.Event Unit)
    (callbacks : ∀ packets, ProductSafe (callback packets)) :
    ProductSafe (Driver.pollObserved Journal.hooks pid budget callback) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.pollObserved
  rw [show Journal.hooks.candidateEnter = (fun _ _ => pure 0) from rfl,
    show Journal.hooks.candidateLeave = (fun _ => pure ()) from rfl,
    AuthenticatedEffects.CandidatePoll.neutral]
  change PrefixPreserves ProductInv Safe
    (AuthenticatedEffects.IndexedPoll.sourceWith _
      (AuthenticatedEffects.TransportDriver.counter Journal.Event.replay)
      (fun peer pkt ep => liftWGObserver (Driver.consumeObserved Journal.hooks peer pkt ep))
      (napiGroReceivePrefix callback) (napiGroFlushAllPrefix callback) pid budget)
  unfold AuthenticatedEffects.IndexedPoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (nonce_product_head napiGroReceivePrefix
       exact napiGroReceivePrefix_preserves callback (fun _ _ hi => hi.2) callbacks _ _)
    | (nonce_product_head napiGroFlushAllPrefix
       exact napiGroFlushAllPrefix_preserves callback (fun _ _ hi => hi.2) callbacks _)
    | (nonce_product_head AuthenticatedEffects.TransportDriver.counter; exact counter _ _)
    | (nonce_product_head liftWGObserver
       apply product_state
       change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
       first
         | (nonce_source_head Driver.consumeObserved; exact consume _ _ _)
         | (apply state_lift; intro h
            try rw [HandshakeSecurity.Responder.DriverCuts.getPeer_twice]
            try unfold WG.andM
            try simp (config := {zeta := false}) only [branch,invariant,unsupported]
            repeat' origin_poll_frame
            done))
    | (nonce_product_head Pure.pure; exact product_pure _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ForIn.forIn
       apply product_loop
       intro x b
       change PrefixPreserves ProductInv Safe _)
    | split
    | (session_origin_intro_forall; try dsimp only)

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
