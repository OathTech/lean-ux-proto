import Leanux.Proofs.WG.Queues.CurrentSlotHistory
import Leanux.Proofs.WG.Origins.OwnerLifecycle

/-! The actual TX socket and worker paths preserve three-slot compatibility.
Saved peer writes are checked against their source getter; normal errno and
all original Stops remain unchanged. -/
namespace Leanux.Proofs.WG.CurrentSlots.TxSource
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues
open CurrentSlots

macro "slot_tx_source_step" : tactic => `(tactic| first
  | (allocation_release_lift_from Net.M; exact store_preserves (liftRouting_sameWGStore _))
  | (allocation_release_head liftRouting; exact store_preserves (liftRouting_sameWGStore _))
  | (allocation_release_head getRouting
     exact store_preserves (liftRouting_sameWGStore
       ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))))
  | (allocation_release_head modify
     apply hoare_modify
     intro w hi
     exact hi)
  | slot_traffic_step)

private theorem dstCacheGet_preserves (pid : PeerId) (gen : Nat) :
    Preserves Inv (dstCacheGet pid gen) := by
  apply fields_preserves (project := id)
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' slot_fields_step initial

private theorem dstCacheSet_preserves (pid : PeerId) (src gen dev : Nat) :
    Preserves Inv (dstCacheSet pid src gen dev) := by
  unfold dstCacheSet
  repeat' slot_tx_source_step

theorem tunnelXmit_preserves (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    Preserves Inv ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact store_preserves (loopbackSend_kernel _ _))
    | (rx_retention_head socketPort
       exact store_preserves (socketPort_sameStore _))
    | slot_tx_source_step

private theorem send4ClearSrc_preserves cache : Preserves Inv (send4ClearSrcSource cache) := by
  unfold send4ClearSrcSource
  repeat' first
    | slot_tx_source_step

private theorem send4Finish_preserves e bytes ds exactRx route : Preserves Inv (send4FinishSource e bytes ds exactRx route) := by
  unfold send4FinishSource
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact tunnelXmit_preserves _ _ _ _ _)
    | slot_tx_source_step

private theorem send4RouteDone_preserves e cache bytes ds exactRx gen fallback rt :
    Preserves Inv (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  unfold send4RouteDoneSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact dstCacheSet_preserves _ _ _ _)
    | (rx_retention_head send4FinishSource; exact send4Finish_preserves _ _ _ _ _)
    | slot_tx_source_step

private theorem send4Retry_preserves e cache bytes ds exactRx gen fallback srcIf rt :
    Preserves Inv (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  unfold send4RetrySource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact send4ClearSrc_preserves _)
    | (rx_retention_head dstCacheReset; exact fields_preserves (project := id) (dstCacheReset_fields _))
    | (rx_retention_head send4RouteDoneSource; exact send4RouteDone_preserves _ _ _ _ _ _ _ _)
    | slot_tx_source_step

private theorem send4Miss_preserves e cache bytes ds exactRx gen fallback saddr srcIf :
    Preserves Inv (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  unfold send4MissSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact send4ClearSrc_preserves _)
    | (rx_retention_head dstCacheReset; exact fields_preserves (project := id) (dstCacheReset_fields _))
    | (rx_retention_head send4RetrySource; exact send4Retry_preserves _ _ _ _ _ _ _ _ _)
    | slot_tx_source_step

private theorem send4AfterCache_preserves e cache bytes ds exactRx gen saddr srcIf route :
    Preserves Inv (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  unfold send4AfterCacheSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact send4Miss_preserves _ _ _ _ _ _ _ _ _)
    | (rx_retention_head send4FinishSource; exact send4Finish_preserves _ _ _ _ _)
    | slot_tx_source_step

theorem send4_preserves e cache bytes ds exactRx : Preserves Inv (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  unfold send4Source
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact dstCacheGet_preserves _ _)
    | (rx_retention_head send4AfterCacheSource; exact send4AfterCache_preserves _ _ _ _ _ _ _ _ _)
    | slot_tx_source_step

theorem send6_preserves (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Preserves Inv (send6 e cache bytes ds exactRx) := by
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact dstCacheGet_preserves _ _)
    | (rx_retention_head dstCacheReset; exact fields_preserves (project := id) (dstCacheReset_fields _))
    | (rx_retention_head dstCacheSet; exact dstCacheSet_preserves _ _ _ _)
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact tunnelXmit_preserves _ _ _ _ _)
    | slot_tx_source_step

private theorem sendSkb_preserves (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Preserves Inv (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4; exact send4_preserves _ _ _ _ _)
    | (rx_retention_head send6; exact send6_preserves _ _ _ _ _)
    | slot_tx_source_step

private theorem dataSent_preserves (pid : PeerId) : Preserves Inv (timersDataSent pid) := by
  unfold timersDataSent modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp Inv)
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp Inv)
    | (rx_retention_head armTimer; exact armTimer_preserves _ _ _ _)
    | slot_traffic_step

private theorem fresh_preserves (pid : PeerId) : Preserves Inv (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact sendQueuedHandshakeInitiation_preserves _ _)
    | slot_traffic_step

private theorem complete_preserves (pid : PeerId) (item : List SkbId) :
    Preserves Inv (createDataDone pid item) := by
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) := hoare_liftAmbient a Inv
  have skb {α : Type} (a : SkbM α) : Preserves Inv (liftSkb a) := by slot_packet_step
  have traversal := timersTraversal_preserves pid
  have authenticated : Preserves Inv (timersAnyAuthenticatedPacketSent pid) := delTimer_preserves pid .sendKeepalive
  have send := sendSkb_preserves pid
  have dataSent := dataSent_preserves pid
  have fresh := fresh_preserves pid
  routing_tx_source [createDataDone] using [traversal,authenticated,send,dataSent,fresh,skb,ambient]

theorem txStep_preserves (pid : PeerId) :
    Preserves Inv (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  let P := Inv
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by slot_packet_step
  have complete (item : List SkbId) : Preserves P (createDataDone pid item) := complete_preserves _ _
  have key (kp : Option KeypairId) : Preserves P (keypairPut kp false) := by slot_traffic_step
  have put : Preserves P (peerPut (some pid)) := by slot_traffic_step
  have dispose (item : List SkbId) (kp : KeypairId) : Preserves P (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [skb,key,put]
  have update (f : Peer → Peer) (hf : ∀ p, Affiliation.peerCell (f p) = Affiliation.peerCell p) :
      Preserves P (do let p ← getPeer pid; setPeer pid (f p)) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.update_peer) pid f hf
  have drop : Preserves P (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.dropPeeked}) :=
    update _ (fun _ => rfl)
  have body (first : Option (List SkbId)) : Preserves P (TxDisposition.bodySource pid first) := by
    unfold TxDisposition.bodySource
    simp only [getPeer_twice]
    apply preserves_bind
    · routing_tx_source [WG.andM] using [skb,ambient]
    · intro go
      cases go with
      | false => exact preserves_pure false
      | true =>
        simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
        cases first with
        | none => exact ambient (AmbientM.invariant "unreachable")
        | some item =>
          cases hh : item.head? with
          | none => simp only [hh]; exact ambient (AmbientM.invariant "an empty ring item")
          | some headId =>
            simp only [hh]
            apply preserves_bind (skb (SkbStore.getTx headId))
            intro head
            apply preserves_bind drop
            intro _
            routing_tx_source [] using [complete,dispose,ambient]
  unfold TxDisposition.stepSource
  apply preserves_bind (show Preserves P (getPeer pid) from by slot_traffic_step)
  intro p
  apply preserves_bind (store_preserves (prevQueuePeek_sameWGStore p.txQueue))
  intro out
  rcases out with ⟨first,queue⟩
  exact preserves_bind (update (fun p => {p with txQueue := queue}) (fun _ => rfl)) (fun _ => body first)

/-- The actual product callback is arbitrary and preserves the slot invariant. -/
theorem txIter_preserves (pid : PeerId) (need : Leanux.M Bool)
    (hn : Preserves (fun w : World => Inv w.wg) need) :
    Preserves (fun w : World => Inv w.wg) (txIter pid need) := by
  let P := fun w : World => Inv w.wg
  have step : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product Inv _ (txStep_preserves pid)
  have needSpec : Preserves P need := hn
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  routing_tx_source [txIter,workerIter] using [step,needSpec,ambient]

/-- Original lifetime observer, arbitrary incoming history and exact Stops. -/
theorem tx_observed (pid : PeerId) :
    PrefixPreserves (fun _ w => Inv w.wg) (fun _ => True)
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (txIterPrefix_erases pid (erasesPrefix_lift _)))
    (txIter_preserves pid _ (product_store_preserves (condResched_sameKernel .txWorker)))

end Leanux.Proofs.WG.CurrentSlots.TxSource
