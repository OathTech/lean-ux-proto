import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueJournalDeferred
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! Actual ingress validates the queue input; fixture sends and NAPI preserve
it through their native callbacks and recorded marker scopes. -/
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity
variable {E : Type} {Safe : List E → Prop} {hooks : Driver.Hooks E}
  {ρ : E → Option TransmitSecurity.Journal.Event}

theorem state_neutral {P : List UInt8 → Prop} {g : WGPrefix E α} {f : α → β} {value : β}
    (history : Driver.StateHistorySafe Safe g)
    (projects : StateProjectsPrefix ρ f g (pure value)) : StateSafe P Safe g := by
  apply checked_state history
  intro w a h result v b before run
  have same:=congrArg Prod.fst (projects w a h)
  change (Except.ok ((value,w),a) : Except Stop ((β × WGWorld) × Ambient)) =
    (runWGPrefix g w a h).1.map (fun ((x,u),b)=>((f x,u),b)) at same
  rw [run] at same
  simp only [Except.map,Except.ok.injEq,Prod.mk.injEq] at same
  exact same.1.2 ▸ before

theorem fixture (c : Contracts P Safe hooks ρ) (trigger : AuthenticatedEffects.FixtureEffects.Trigger)
    (body : WGPrefix E α) (keeps : StateSafe P Safe body) :
    StateSafe P Safe (AuthenticatedEffects.FixtureEffects.runWith (Driver.fixtureOps hooks) trigger body) := by
  obtain ⟨scopeMap,enter,leave⟩:=c.projects.fixture
  exact AuthenticatedEffects.FixtureEffects.run_preserves _ _ _ (fun _ _ _ before=>before.2)
    (state_neutral (c.quiet.fixtureEnter trigger) (enter trigger))
    (fun token=>state_neutral (c.quiet.fixtureLeave token) (leave token)) keeps

theorem ingress (c : Contracts Valid Safe hooks ρ) (msg : List UInt8) (src : SkbSource) :
    ProductSafe Valid Safe (Driver.receiveEntryObserved hooks msg src) := by
  apply checked_product (Driver.receiveEntry_history hooks c.quiet.peerRelease msg src)
  intro w h result v before run
  have projected := Projection.product (Driver.receiveEntry_projects c.projects msg src)
    (Driver.receiveEntry_projects TransmitSecurity.Journal.hooks_projects msg src)
  rw [Driver.receiveEntry_lift Driver.nonceHooks rfl, liftWGObserver_lift] at projected
  have plain := DriverOwnership.product_native projected (erasesPrefix_lift _) w v h run
  rw [liftWG_run] at plain
  cases nativeRun : ((wgReceive msg src).run w.wg).run w.ambient with
  | error e => simp [nativeRun, Except.map] at plain
  | ok output =>
    obtain ⟨⟨value,g⟩,a⟩ := output
    simp only [nativeRun, Except.map, Except.ok.injEq, Prod.mk.injEq] at plain
    rcases plain with ⟨_,same⟩
    subst v
    exact (hoare_iff_run_ambient _ _ _).mp (receive msg src) w.wg w.ambient value g a before nativeRun

theorem inline_poll (c : Contracts P Safe hooks ρ) :
    ProductSafe P Safe (Driver.inlinePollObserved hooks) := by
  have history : Driver.ProductHistorySafe Safe (Driver.inlinePollObserved hooks) :=
    (show Driver.inlinePollObserved (quietHooks hooks)=Driver.inlinePollObserved hooks from rfl) ▸ Driver.inline_history c.quiet
  have projected:=Projection.product (Driver.inline_projects c.projects) (Driver.inline_projects TransmitSecurity.Journal.hooks_projects)
  rw [Driver.nonce_inlinePollObserved_eq] at projected
  have native : SameView HandshakeLengths.productView Env.pollScheduledInline := by
    have poll:=fun pid=>rxPoll_cell pid NAPI_POLL_WEIGHT _ stackForM_cell
    handshake_poll_source [Env.pollScheduledInline] using [poll] with []
  exact product_native history projected Nonce.inlinePollObserved_erases (product_frame native)

theorem multicast (family addr : Nat) : ProductSafe P Safe (Driver.multicastObserved family addr) := by
  apply product_store
  intro initial
  change Preserves (fun w : World=>productStoreView w=initial) _
  have loop : Preserves (fun w : World=>productStoreView w=initial)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    liftWG_sameProductStore _ (loopbackSend_kernel [] true) initial
  have ambient {α : Type} (action : AmbientM α) :
      Preserves (fun w : World=>productStoreView w=initial) (monadLift action : Leanux.M α) :=
    productAmbient_spec action _ (fun _ _ before=>before)
  routing_tx_source [Env.xmitMulticastLoop] using [loop,ambient]

theorem drain (what : String) (flags : List Bool) : ProductSafe P Safe (Driver.drainObserved what flags) :=
  product_store _ (Nonce.Frames.drained what flags)

theorem wg_stable (h : List E) (w v : World) (same : wgStoreView v.wg=wgStoreView w.wg)
    (before : ProductInv P Safe h w) : ProductInv P Safe h v := by
  refine ⟨transport ?_ before.1,before.2⟩
  exact congrArg (fun store : WGStoreView=>store.dev.map fun d=>d.handshakeQueue) same

theorem inject (c : Contracts Valid Safe hooks ρ) (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe Valid Safe (Driver.injectObserved hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves (fun _ _ before=>before.2) stable _ _ _ (ingress c) (crypt c) drain
    family port msg tos ll dest

theorem after_batch (c : Contracts P Safe hooks ρ) : ProductSafe P Safe (Driver.afterBatchObserved hooks) := by
  change PrefixPreserves (ProductInv P Safe) Safe _
  unfold Driver.afterBatchObserved AuthenticatedEffects.DeliverySource.afterBatchWith
  repeat' first
    | (nonce_product_head Driver.cryptObserved; exact crypt c)
    | (nonce_product_head Driver.sendWorkersObserved; exact send_workers c)
    | (nonce_product_head Driver.scheduleObserved; exact schedule c _)
    | (nonce_product_head Driver.drainObserved; exact drain _ _)
    | handshake_journal_deferred_step c

theorem flood (c : Contracts Valid Safe hooks ρ) (count port family : Nat) (messages : List (List UInt8)) :
    ProductSafe Valid Safe (Driver.floodObserved hooks count port family messages) :=
  TrafficSource.flood_preserves (fun _ _ before=>before.2) stable _ _ _ _ (ingress c) (inline_poll c)
    (after_batch c) drain count port family messages

theorem batch_item (c : Contracts Valid Safe hooks ρ) (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductSafe Valid Safe (Driver.batchItemObserved hooks d cqes item) :=
  batchItemWith_preserves (fun _ _ before=>before.2) wg_stable _ _ _ _ (ingress c) (inline_poll c) multicast
    (fun family addr packets mtu=>state_product (fixture c _ _ (transmit c family addr packets mtu))) d cqes item

theorem batch (c : Contracts Valid Safe hooks ρ) (items : List Env.BatchItem) :
    ProductSafe Valid Safe (Driver.batchObserved hooks items) :=
  TrafficSource.batch_preserves (fun _ _ before=>before.2) stable _ _ (batch_item c) (after_batch c) items

theorem syscall_xmit (c : Contracts P Safe hooks ρ) (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductSafe P Safe (Driver.syscallXmitObserved hooks family addr payload opts) :=
  syscallXmitWith_preserves (fun _ _ before=>before.2) wg_stable _ _ multicast
    (fun family addr packets mtu=>state_product (fixture c _ _ (transmit c family addr packets mtu))) family addr payload opts

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
