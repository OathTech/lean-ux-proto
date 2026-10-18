import Leanux.Proofs.WG.Queues.HolderFrames
import Leanux.Proofs.WG.Queues.SendEnvironment
import Leanux.Proofs.WG.Packets.PublicationHandshakeSend

/-! Actual worker field frames retain the complete passive account and every
surviving TX queue. Final peer deletion is allowed. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private theorem store {α : Type} {action : WG.M α} (ha : SameWGStore action) (initial) :
    Preserves (Frame initial) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact hi.trans (Frame.of_store ((ProjectedAction.iff_run_ambient _ _ _).mp ha w a x v b run))

private theorem read_bind (initial : WGWorld) {α : Type} (pid : PeerId) (f : Peer → WG.M α)
    (hf : ∀ p, handoffTxView initial pid = some p.txQueue.all → Preserves (Frame initial) (f p)) :
    Preserves (Frame initial) (getPeer pid >>= f) := by
  apply hoare_bind _ _ (show Hoare (getPeer pid) (Frame initial)
    (fun p w => Frame initial w ∧ handoffTxView initial pid = some p.txQueue.all) from ?_)
  · intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b hi run
    exact (hoare_iff_run_ambient _ _ _).mp (hf p hi.2) w a x v b hi.1 run
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi run
    obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal pid w v p a b run
    exact ⟨hi,hi.tx pid p.txQueue.all (by simp [handoffTxView,hd,hp])⟩

private theorem set_saved (initial : WGWorld) (pid : PeerId) (p : Peer)
    (saved : handoffTxView initial pid = some p.txQueue.all) :
    Preserves (Frame initial) (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  cases run
  refine ⟨?_,?_,?_⟩
  · simpa only [passiveView,Option.map_map,Function.comp_def] using hi.passive
  · simpa only [sendView,Option.map_map,Function.comp_def] using hi.send
  · intro q batches found
    cases hd : w.dev with
    | none => simp [handoffTxView,hd] at found
    | some d =>
      simp only [handoffTxView,hd,Option.map_some,Option.bind_some,
        Std.TreeMap.getElem?_insert,Std.LawfulEqOrd.compare_eq_iff_eq] at found
      by_cases same : pid = q
      · subst q
        simp only [ite_true,Option.map_some,Option.some.injEq] at found
        exact found ▸ saved
      · apply hi.tx q batches
        simpa only [handoffTxView,hd,Option.bind_some,ite_eq_right same] using found

private theorem modify_frame (f : Device → Device)
    (base : ∀ d, (f d).peerList = d.peerList)
    (send : ∀ d, (f d).sendWorkQueue = d.sendWorkQueue)
    (clear : ∀ d, (f d).clearWorkQueue = d.clearWorkQueue)
    (tx : ∀ (d : Device) (q : PeerId) (batches : List (List SkbId)), ((f d).peers[q]?).map (fun p : Peer => p.txQueue.all) = some batches →
      (d.peers[q]?).map (fun p : Peer => p.txQueue.all) = some batches) (initial) :
    Preserves (Frame initial) (modifyDev f) := by
  apply hoare_modify
  intro w hi
  refine ⟨?_,?_,?_⟩
  · simpa only [passiveView,Option.map_map,Function.comp_def,base,clear] using hi.passive
  · simpa only [sendView,Option.map_map,Function.comp_def,send] using hi.send
  · intro q batches found
    apply hi.tx q batches
    cases hd : w.dev with
    | none => simp [handoffTxView,hd] at found
    | some d =>
      simpa only [handoffTxView,hd,Option.bind_some] using
        tx d q batches (by simpa only [handoffTxView,hd,Option.map_some,Option.bind_some] using found)

private theorem timer_tx (p : Peer) (timer : PeerTimer) (value : Option UInt64) :
    (p.setTimer timer value).txQueue.all = p.txQueue.all := by cases timer <;> rfl

private theorem wheel_tx (p : Peer) (timer : PeerTimer) (value : Option WheelEntry) :
    (p.setWheel timer value).txQueue.all = p.txQueue.all := by cases timer <;> rfl

macro "holder_work_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (env_bind_head getPeer; apply read_bind $initial; intro p saved)
  | (rx_retention_head setPeer; apply set_saved $initial; first | assumption | (simp only [timer_tx,wheel_tx]; assumption))
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a p v b hi hr
     simpa only [(getPeer_normal _ w v p a b hr).1] using hi)
  | (rx_retention_head getDev; exact store getDev_sameWGStore $initial)
  | (rx_retention_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b hi hr
     simpa only [(KeyTimes.getKeypair_return _ w v k a b hr).1] using hi)
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from Net.M; exact store (liftRouting_sameWGStore _) $initial)
  | (rx_retention_head liftRouting; exact store (liftRouting_sameWGStore _) $initial)
  | (rx_retention_head getRouting; exact store (liftRouting_sameWGStore
      ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))) $initial)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM
     apply hoare_liftIndex
     intro w d table hi hd
     exact hi.trans (by constructor <;> first | (simp [passiveView,sendView,hd]) |
       (intro q xs h; simpa [handoffTxView,hd] using h)))
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev
     apply modify_frame
     · intro d; rfl
     · intro d; rfl
     · intro d; rfl
     · intro d q batches found
       first
       | exact found
       | (simp only [Std.TreeMap.getElem?_erase,Std.LawfulEqOrd.compare_eq_iff_eq] at found
          split at found
          · simp at found
          · exact found))
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi.trans (Frame.of_store rfl))
  | (rx_retention_head Functor.discard
     apply discard_view_spec id (Frame $initial)
     change Preserves (Frame $initial) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi hr
     cases hr)
  | rx_retention_step)

theorem peerPut_frame (pid : Option PeerId) (initial) : Preserves (Frame initial) (peerPut pid) := by
  unfold peerPut refcountDecAndTest retirePeerUnits
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,
    invariant,unsupported,modifyAmbient]
  repeat' holder_work_step initial

theorem keypairPut_frame (kid : Option KeypairId) (now : Bool) (initial) :
    Preserves (Frame initial) (keypairPut kid now) := by
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' holder_work_step initial

theorem handshakeClear_frame (pid : PeerId) (initial) :
    Preserves (Frame initial) (handshakeClear pid) := by
  unfold handshakeClear handshakeZero
  repeat' holder_work_step initial

theorem keypairsClear_frame (pid : PeerId) (initial) :
    Preserves (Frame initial) (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' first
    | (rx_retention_head keypairPut; exact keypairPut_frame _ _ initial)
    | holder_work_step initial

theorem queuedClear_frame (pid : PeerId) (initial) :
    Preserves (Frame initial) (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact preserves_bind (handshakeClear_frame pid initial) (fun _ =>
    preserves_bind (keypairsClear_frame pid initial) (fun _ => peerPut_frame (some pid) initial))

private theorem place_preserves (pid : PeerId) (t : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) (initial) : Preserves (Frame initial) (placeOnWheel pid t expires clk unit) := by
  unfold placeOnWheel
  simp (config := {zeta := false}) only [hidden,peekHiddenSite,invariant]
  repeat' holder_work_step initial

private theorem arm_preserves (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64) (initial) : Preserves (Frame initial) (armTimer pid timer delay jc) := by
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient,hidden,invariant,unsupported]
  repeat' first
    | rxstack_preserves_join
    | (rx_retention_head placeOnWheel; exact place_preserves _ _ _ _ _ initial)
    | holder_work_step initial

private theorem del_preserves (pid : PeerId) (timer : PeerTimer) (initial) :
    Preserves (Frame initial) (delTimer pid timer) := by
  unfold delTimer
  repeat' holder_work_step initial

private theorem mod_preserves (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) (initial) :
    Preserves (Frame initial) (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (Frame initial))
    | (rx_retention_head armTimer; exact arm_preserves _ _ _ _ initial)
    | holder_work_step initial

macro "holder_work_crypto " initial:term : tactic => `(tactic| first
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Frame $initial))
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (Frame $initial))
  | (rx_retention_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (Frame $initial))
  | (rx_retention_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (Frame $initial))
  | (rx_retention_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (Frame $initial)))

private theorem timersTraversal_frame (pid : PeerId) (initial) : Preserves (Frame initial) (timersTraversal pid) := by
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp]
  repeat' first
    | (allocation_release_head modPeerTimer; exact mod_preserves _ _ _ _ initial)
    | holder_work_step initial

private theorem timersAnyAuthenticatedPacketSent_frame (pid : PeerId) :
    ∀ initial, Preserves (Frame initial) (timersAnyAuthenticatedPacketSent pid) := by
  intro initial
  change Preserves (Frame initial) _
  unfold timersAnyAuthenticatedPacketSent
  repeat' first
    | (rx_retention_head delTimer
       exact del_preserves _ _ initial)
    | holder_work_step initial

private theorem timersHandshakeInitiated_frame (pid : PeerId) :
    ∀ initial, Preserves (Frame initial) (timersHandshakeInitiated pid) := by
  intro initial
  change Preserves (Frame initial) _
  unfold timersHandshakeInitiated modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (Frame initial))
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (Frame initial))
    | (rx_retention_head armTimer
       exact arm_preserves _ _ _ _ initial)
    | holder_work_step initial

private theorem dstCacheReset_frame (pid : PeerId) : ∀ initial, Preserves (Frame initial) (dstCacheReset pid) := by
  intro initial
  change Preserves (Frame initial) _
  unfold dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' holder_work_step initial

private theorem createInitiation_frame (pid : PeerId) : ∀ initial, Preserves (Frame initial) (createInitiation pid) := by
  intro initial
  change Preserves (Frame initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first | holder_work_crypto initial | holder_work_step initial

private theorem addMacToPacket_frame (pid : PeerId) (msg : List UInt8) :
    ∀ initial, Preserves (Frame initial) (addMacToPacket pid msg) := by
  intro initial
  change Preserves (Frame initial) _
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first | holder_work_crypto initial | holder_work_step initial

private theorem dstCacheGet_frame (pid : PeerId) (gen : Nat) : ∀ initial, Preserves (Frame initial) (dstCacheGet pid gen) := by
  intro initial
  change Preserves (Frame initial) _
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' holder_work_step initial

private theorem dstCacheSet_frame (pid : PeerId) (src gen dev : Nat) : ∀ initial, Preserves (Frame initial) (dstCacheSet pid src gen dev) := by
  intro initial
  change Preserves (Frame initial) _
  unfold dstCacheSet
  repeat' holder_work_step initial

private theorem tunnelXmit_frame (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    ∀ initial, Preserves (Frame initial) ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  change Preserves (Frame initial) _
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact store (loopbackSend_kernel _ _) initial)
    | (rx_retention_head socketPort
       exact store (socketPort_sameStore _) initial)
    | holder_work_step initial

private theorem send4ClearSrc_frame cache : ∀ initial, Preserves (Frame initial) (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  change Preserves (Frame initial) _
  repeat' first
    | holder_work_step initial

private theorem send4Finish_frame e bytes ds exactRx route : ∀ initial, Preserves (Frame initial) (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  change Preserves (Frame initial) _
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact tunnelXmit_frame _ _ _ _ _ initial)
    | holder_work_step initial

private theorem send4RouteDone_frame e cache bytes ds exactRx gen fallback rt :
    ∀ initial, Preserves (Frame initial) (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  change Preserves (Frame initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact dstCacheSet_frame _ _ _ _ initial)
    | (rx_retention_head send4FinishSource; exact send4Finish_frame _ _ _ _ _ initial)
    | holder_work_step initial

private theorem send4Retry_frame e cache bytes ds exactRx gen fallback srcIf rt :
    ∀ initial, Preserves (Frame initial) (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  change Preserves (Frame initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact send4ClearSrc_frame _ initial)
    | (rx_retention_head dstCacheReset; exact dstCacheReset_frame _ initial)
    | (rx_retention_head send4RouteDoneSource; exact send4RouteDone_frame _ _ _ _ _ _ _ _ initial)
    | holder_work_step initial

private theorem send4Miss_frame e cache bytes ds exactRx gen fallback saddr srcIf :
    ∀ initial, Preserves (Frame initial) (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  change Preserves (Frame initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact send4ClearSrc_frame _ initial)
    | (rx_retention_head dstCacheReset; exact dstCacheReset_frame _ initial)
    | (rx_retention_head send4RetrySource; exact send4Retry_frame _ _ _ _ _ _ _ _ _ initial)
    | holder_work_step initial

private theorem send4AfterCache_frame e cache bytes ds exactRx gen saddr srcIf route :
    ∀ initial, Preserves (Frame initial) (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  change Preserves (Frame initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact send4Miss_frame _ _ _ _ _ _ _ _ _ initial)
    | (rx_retention_head send4FinishSource; exact send4Finish_frame _ _ _ _ _ initial)
    | holder_work_step initial

private theorem send4_frame e cache bytes ds exactRx : ∀ initial, Preserves (Frame initial) (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  change Preserves (Frame initial) _
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact dstCacheGet_frame _ _ initial)
    | (rx_retention_head send4AfterCacheSource; exact send4AfterCache_frame _ _ _ _ _ _ _ _ _ initial)
    | holder_work_step initial

private theorem send6_frame (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ∀ initial, Preserves (Frame initial) (send6 e cache bytes ds exactRx) := by
  intro initial
  change Preserves (Frame initial) _
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact dstCacheGet_frame _ _ initial)
    | (rx_retention_head dstCacheReset; exact dstCacheReset_frame _ initial)
    | (rx_retention_head dstCacheSet; exact dstCacheSet_frame _ _ _ _ initial)
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact tunnelXmit_frame _ _ _ _ _ initial)
    | holder_work_step initial

private theorem sendBufferToPeer_frame (pid : PeerId) (bytes : List UInt8) : ∀ initial, Preserves (Frame initial) (sendBufferToPeer pid bytes) := by
  intro initial
  change Preserves (Frame initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head send4; exact send4_frame _ _ _ _ _ initial)
    | (rx_retention_head send6; exact send6_frame _ _ _ _ _ initial)
    | holder_work_step initial

theorem sendHandshakeInitiation_frame (pid : PeerId) : ∀ initial, Preserves (Frame initial) (sendHandshakeInitiation pid) := by
  intro initial
  change Preserves (Frame initial) _
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createInitiation; exact createInitiation_frame _ initial)
    | (rx_retention_head addMacToPacket; exact addMacToPacket_frame _ _ initial)
    | (rx_retention_head timersTraversal; exact timersTraversal_frame _ initial)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact timersAnyAuthenticatedPacketSent_frame _ initial)
    | (rx_retention_head timersHandshakeInitiated; exact timersHandshakeInitiated_frame _ initial)
    | (rx_retention_head sendBufferToPeer; exact sendBufferToPeer_frame _ _ initial)
    | holder_work_crypto initial
    | holder_work_step initial

theorem handshakeSendWorker_frame (pid : PeerId) (initial) : Preserves (Frame initial) (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact preserves_bind (sendHandshakeInitiation_frame pid initial) (fun _ => peerPut_frame (some pid) initial)

end Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames
