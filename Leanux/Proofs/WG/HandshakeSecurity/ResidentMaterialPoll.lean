import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialPollFrames

/-! The actual indexed RX poll carries TX key material through authenticated
completion and its exact stack callback. No endpoint-erasure argument is used
to invent an internal material receipt. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def ProductInv (h : List Journal.Event) (w : World) : Prop := Carrier h w.wg
abbrev ProductSafe (g : PrefixM Journal.Event α) := PrefixPreserves ProductInv Safe g

theorem product_state {g : WGPrefix Journal.Event α} (safe : CarrierSafe g) :
    ProductSafe (liftWGObserver g) := safe.liftWGObserver

theorem product_pure (x : α) : ProductSafe (pure x) :=
  PrefixPreserves.pure (fun _ _ hi => hi.1.2) x

theorem product_loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → PrefixM Journal.Event (ForInStep β)) (safe : ∀ x b, ProductSafe (g x b)) :
    ProductSafe (forIn xs b g) :=
  PrefixEnsures.forInInvariant xs b g (fun _ h w => ProductInv h w) Safe (fun _ _ _ hi => hi.1.2) safe

theorem product_quiet {g : PrefixM Journal.Event α} {action : Leanux.M α}
    (app : Appends g) (quiet : HistoryFrame Journal.encryption? g) (erase : ErasesPrefix g action)
    (material : ∀ h, Preserves (fun w : World => Inv h w.wg) action)
    (bounds : Preserves (fun w : World => Bounds w.wg) action) : ProductSafe g := by
  intro w h hi
  obtain ⟨suffix,eq⟩ := app w h
  have noCipher : suffix.filterMap Journal.encryption? = [] := by
    have same := quiet w h
    rw [eq,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap Journal.encryption? with
    | nil => rfl
    | cons e es =>
      simp only [List.length_append,found,List.length_cons] at lengths
      omega
  have safe : Safe (runPrefix g w h).2 := by rw [eq]; exact hi.1.2.quiet_suffix noCipher
  refine ⟨suffix,eq,safe,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok value =>
    have native := (erase w h).symm.trans result
    have kept := (hoare_iff_run _ _ _).mp (material h) w value.1 value.2 hi.1.1 native
    have bounded := (hoare_iff_run _ _ _).mp bounds w value.1 value.2 hi.2 native
    refine ⟨⟨kept.mono ?_,safe⟩,bounded⟩
    intro e member
    rw [eq]
    exact List.mem_append_left _ member

theorem counter_carrier (skb : SkbId) (pkt : RxPacket) :
    ProductSafe (AuthenticatedEffects.TransportDriver.counter Journal.Event.replay skb pkt) :=
  product_quiet (Appends.lift _).receiptObserved
    (HistoryFrame.receiptObserved (HistoryFrame.lift _ _) (fun _ => rfl))
    (AuthenticatedEffects.TransportDriver.counter_erases _ _ _)
    (fun _ => PublicationPoll.native_product _ _ (NativeFrames.counter pkt.keypair pkt.nonce))
    (PublicationPoll.native_product _ _ (bounds_forget (DriverCuts.carrier_counter pkt.keypair pkt.nonce)))

theorem poll_carrier (pid : PeerId) (budget : Nat) (callback : List (List UInt8) → PrefixM Journal.Event Unit)
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
       exact napiGroReceivePrefix_preserves callback (fun _ _ hi => hi.1.2) callbacks _ _)
    | (nonce_product_head napiGroFlushAllPrefix
       exact napiGroFlushAllPrefix_preserves callback (fun _ _ hi => hi.1.2) callbacks _)
    | (nonce_product_head AuthenticatedEffects.TransportDriver.counter; exact counter_carrier _ _)
    | (nonce_product_head liftWGObserver
       apply product_state
       change StatePrefixPreserves (fun h w _ => Carrier h w) Safe _
       first
         | (nonce_source_head Driver.consumeObserved; exact consume_carrier _ _ _)
         | (apply carrier_lift
            · intro h
              try rw [Queues.getPeer_twice]
              try unfold WG.andM
              try simp (config := {zeta := false}) only [branch,invariant,unsupported]
              repeat' resident_poll_frame
              done
            · apply bounds_forget
              intro labels
              try rw [Queues.getPeer_twice]
              try unfold WG.andM
              try simp (config := {zeta := false}) only [branch,invariant,unsupported]
              repeat' responder_carrier_poll_step labels
              done))
    | (nonce_product_head Pure.pure; exact product_pure _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ForIn.forIn
       apply product_loop
       intro x b
       change PrefixPreserves ProductInv Safe _)
    | split
    | (session_origin_intro_forall; try dsimp only)

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
