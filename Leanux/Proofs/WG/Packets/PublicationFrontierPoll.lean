import Leanux.Proofs.WG.Packets.PublicationIngressNative
import Leanux.Proofs.WG.Packets.PublicationStack

/-! The packet-owner bound accompanies the weak publication anchor through
actual completion, transmit replies, arbitrary callbacks and poll cleanup. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues PublicationCompletion

private theorem configured {α : Type} (a : WG.M α)
    (shape : SameView OwnerCompletion.geometry a)
    (peers : SameView ConfiguredIdentity.view a) (history : List RxHistory.Event) :
    Preserves (Inv history) a :=
  preserves_of_geometry a shape
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured) peers) history

theorem consumeDataDone_preserves (pid : PeerId) (pkt : RxPacket) (ep : Endpoint)
    (history : List RxHistory.Event) : Preserves (Inv history) (consumeDataDone pid pkt ep) :=
  preserves_of_geometry _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.done_geometry) pid pkt ep)
    (PublicationCompletion.consumeDataDone_peers pid pkt ep) history

theorem sendStagedPackets_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (sendStagedPackets pid) :=
  preserves_of_geometry _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.staged_geometry) pid)
    (PublicationCompletion.sendStagedPackets_peers pid) history

theorem wgXmit_preserves (family addr : Nat) (packets : List WG.Packet) (mtu : Nat)
    (history : List RxHistory.Event) : Preserves (Inv history) (wgXmit family addr packets mtu) :=
  preserves_of_geometry _ (PublicationStack.wgXmit_geometry family addr packets mtu)
    (PublicationStack.wgXmit_peers family addr packets mtu) history

private theorem store {α : Type} (a : WG.M α) (frame : SameWGStore a)
    (history : List RxHistory.Event) : Preserves (Inv history) a := store_preserves frame history

private theorem product_store {α : Type} (a : Leanux.M α) (frame : SameProductStore a)
    (history : List RxHistory.Event) : Preserves (fun w : World => Inv history w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi hr
  have fields := (ProjectedAction.iff_run _ _ _).mp frame w result v hr
  have dev : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) fields
  apply hi.transport_cells
  · intro id pkt cell _
    exact ⟨by simpa only [RxDisposition.nativeRxStore,dev] using cell,
      by simp only [packetStamp,dev]⟩
  · exact FrontiersLe.of_eq (by simp only [frontier,dev])
  · intro pid d p hd hp
    exact ⟨d,p,dev.symm.trans hd,hp,rfl⟩

theorem reply4_preserves (dst : Nat) (bytes : List UInt8) (history : List RxHistory.Event) :
    Preserves (fun w : World => Inv history w.wg) (Leanux.Env.Stack.reply4 dst bytes) := by
  let P := fun w : World => Inv history w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product _ _ (store _ (liftRouting_sameWGStore a) history)
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    PublicationPoll.native_product _ _ (store _ getDev_sameWGStore history)
  have send (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    PublicationPoll.native_product _ _ (wgXmit_preserves family addr packets mtu history)
  have discarded {α : Type} (a : Leanux.M α) (ha : Preserves P a) : Preserves P (discard a) :=
    discard_view_spec id P a ha
  rxstack_preserves_source [Leanux.Env.Stack.reply4,skipCut,unsupported]
    using [dev,send,ambient,routing,discarded]

theorem receive4_preserves (bytes : List UInt8) (history : List RxHistory.Event) :
    Preserves (fun w : World => Inv history w.wg) (Leanux.Env.Stack.receive4 bytes) := by
  let P := fun w : World => Inv history w.wg
  have stopped (a : Leanux.M Unit) (hs : ∀ w, ∃ e, a.run w = .error e)
      (next : Unit → Leanux.M Unit) : Preserves P (a >>= next) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.stopped_bind) a hs next P
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_,rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_,rfl⟩) tail
  have excludedAlone (row : String) : Preserves P (Leanux.Env.Stack.excluded row) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    obtain ⟨e,he⟩ := stackExcluded_failure row w
    rw [he] at hr
    contradiction
  have route (src dst : Nat) : Preserves P
      (monadLift (monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    PublicationPoll.native_product _ _ (store _ (liftRouting_sameWGStore _) history)
  have read : Preserves P (getWG : Leanux.M WGWorld) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  have write (f : EnvWorld → EnvWorld) : Preserves P (modifyEnv f) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  unfold Leanux.Env.Stack.receive4
  repeat' first
    | (env_bind_head Leanux.Env.Stack.excluded; exact excluded _ _)
    | (env_bind_head Leanux.invariant; exact invalid _ _)
    | (env_bind_head Leanux.unsupported; exact unsupported _ _)
    | (allocation_release_head Leanux.Env.Stack.excluded; exact excludedAlone _)
    | (allocation_release_head Leanux.Env.Stack.reply4; exact reply4_preserves _ _ history)
    | (allocation_release_head MonadLift.monadLift; exact route _ _)
    | (allocation_release_head liftM; exact route _ _)
    | (allocation_release_head getWG; exact read)
    | (allocation_release_head modifyEnv; exact write _)
    | rx_retention_step
    | env_ordinary_head_reduce
    | env_ordinary_head_match

theorem deliverInner_preserves (bytes : List UInt8) (history : List RxHistory.Event) :
    Preserves (fun w : World => Inv history w.wg) (Leanux.Env.deliverInner bytes) := by
  have h4 := receive4_preserves bytes history
  have h6 := product_store _ (stackReceive6_sameKernel bytes) history
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => Inv history w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  rxstack_preserves_source [Leanux.Env.deliverInner,Leanux.Env.Stack.receive,invariant]
    using [h4,h6,ambient]

theorem stack_preserves (packets : List (List UInt8)) (history : List RxHistory.Event) :
    Preserves (fun w : World => Inv history w.wg) (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_preserves bytes history) (fun _ => ih)

private theorem peek_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (peekRxQueue pid) :=
  configured _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationPoll.«0».Leanux.Proofs.WG.PublicationPoll.peek_geometry) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.peek_view) pid) history

private theorem drop_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (dropRxQueue pid) :=
  configured _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationPoll.«0».Leanux.Proofs.WG.PublicationPoll.drop_geometry) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.drop_view) pid) history

private theorem complete_geometry (pid : PeerId) :
    SameView OwnerCompletion.geometry (completeRxQueue pid) := by
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold completeRxQueue
  repeat' completion_step initial

private theorem complete_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (completeRxQueue pid) :=
  configured _ (complete_geometry pid)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.complete_view) pid) history

private theorem counter_preserves (kid : KeypairId) (nonce : Nat) (history : List RxHistory.Event) :
    Preserves (Inv history) (counterValidate kid nonce) :=
  configured _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerPoll.«0».Leanux.Proofs.WG.OwnerPoll.counter_geometry) kid nonce)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.counterValidate_view) kid nonce) history

private theorem readRx_preserves (id : SkbId) (history : List RxHistory.Event) :
    Preserves (Inv history) (getRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a pkt v b hi hr
  exact (Packets.getRxSkb_current id w v pkt a b hr).1 ▸ hi

macro "publication_frontier_poll_native " history:term : tactic => `(tactic| first
  | (rx_retention_head peekRxQueue; exact peek_preserves _ $history)
  | (rx_retention_head dropRxQueue; exact drop_preserves _ $history)
  | (rx_retention_head completeRxQueue; exact complete_preserves _ $history)
  | (rx_retention_head counterValidate; exact counter_preserves _ _ $history)
  | (rx_retention_head consumeDataDone; exact consumeDataDone_preserves _ _ _ $history)
  | (rx_retention_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _) $history)
  | (rx_retention_head getRxSkb; exact readRx_preserves _ $history)
  | (rx_retention_head freeRxSkb; exact freeRxSkb_preserves _ $history)
  | (rx_retention_head keypairPut; exact keypairPut_preserves _ _ $history)
  | (rx_retention_head peerPut; exact peerPut_preserves _ $history)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv $history))
  | rx_retention_step)

/-- The callback remains an arbitrary product action with its exact combined
invariant contract. No exact-frame condition is imposed on that callback. -/
theorem poll (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit) (history : List RxHistory.Event)
    (hc : ∀ xs, Preserves (fun w : World => Inv history w.wg) (callback xs)) :
    Preserves (fun w : World => Inv history w.wg) (rxPoll pid budget callback) := by
  rw [← rxPollGrouped_eq]
  unfold rxPollGrouped
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,invariant,unsupported,WG.andM]
  repeat' first
    | (rx_retention_head napiGroReceive
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groReceive_preserves)
         _ callback hc _ _)
    | (rx_retention_head napiGroFlushAll
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groFlush_preserves)
         _ callback hc _)
    | (allocation_release_lift_from WG.M
       apply PublicationPoll.native_product
       simp only [monadLift_self]
       repeat' publication_frontier_poll_native history)
    | (allocation_release_lift_from AmbientM
       exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => Inv history w.wg)
       intro x b
       change Preserves (fun w : World => Inv history w.wg) _)
    | rx_retention_step

theorem poll_stack (pid : PeerId) (budget : Nat) (history : List RxHistory.Event) :
    Preserves (fun w : World => Inv history w.wg)
      (rxPoll pid budget (fun packets => packets.forM Env.deliverInner)) :=
  poll pid budget _ history (fun packets => stack_preserves packets history)

end Leanux.Proofs.WG.PublicationFrontier
