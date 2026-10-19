import Leanux.Proofs.WG.Origins.ConfiguredMaintenance
import Leanux.Proofs.WG.Origins.CurrentMaintenance
import Leanux.Proofs.WG.Origins.CurrentPeerRetains
import Leanux.Proofs.WG.Peers.ConfiguredTimers
import Leanux.Proofs.WG.Keypairs.Frames.EnvLeaves

/-! Configured identity through concrete handshake construction and socket
transmission. Saved peer cells are retained across each actual write. -/
namespace Leanux.Proofs.WG.ConfiguredHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Queues
open Leanux.Proofs.WG.ConfiguredIdentity

private theorem read_bind (initial : Option ConfiguredIdentity.State) {α : Type}
    (pid : PeerId) (f : Peer → WG.M α)
    (hf : ∀ p, initial.bind (fun s => s.peers pid) = some (cell p) →
      Preserves (fun w => view w = initial) (f p)) :
    Preserves (fun w => view w = initial) (getPeer pid >>= f) := by
  apply hoare_bind _ _ (getPeer_spec (fun s => s = initial) pid)
  intro p
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  have saved := h.2
  rw [h.1] at saved
  exact (hoare_iff_run_ambient _ _ _).mp (hf p saved) w ambient x v ambient' h.1 hr

private theorem set_saved (initial : Option ConfiguredIdentity.State) (pid : PeerId) (p : Peer)
    (hp : initial.bind (fun s => s.peers pid) = some (cell p)) :
    Preserves (fun w => view w = initial) (setPeer pid p) := by
  apply hoare_consequence (setPeer_spec (fun s => s = initial) pid p)
  · intro w h
    exact ⟨h, by rw [h]; exact hp⟩
  · exact fun _ _ h => h

macro "configured_step " initial:term : tactic => `(tactic| first
  | (env_bind_head getPeer; apply read_bind $initial; intro p hp)
  | (rx_retention_head setPeer; apply set_saved $initial; assumption)
  | (rx_retention_head getPeer
     exact hoare_consequence (getPeer_spec (fun s => s = $initial) _)
       (fun _ h => h) (fun _ _ h => h.1))
  | (rx_retention_head getDev; exact (sameWG (project := id) getDev_sameWGStore).wp (fun s => s = $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM
     apply hoare_liftIndex
     intro w d table hi hd
     simpa only [view,hd,Option.map_some,state] using hi)
  | (allocation_release_lift_from Net.M
     exact hoare_liftRouting _ _ (fun _ _ h => h))
  | (rx_retention_head liftRouting; exact hoare_liftRouting _ _ (fun _ _ h => h))
  | (rx_retention_head getRouting
     exact hoare_liftRouting ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
       _ (fun _ _ h => h))
  | (rx_retention_head get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head MonadStateOf.get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev; exact ConfiguredIdentity.modifyDev_spec
      (fun s => s = $initial) _ (fun _ => rfl))
  | (rx_retention_head throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient x v ambient' hi hr
     cases hr)
  | (rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient x v ambient' hi hr
     cases hr)
  | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
  | rx_retention_step)

macro "configured_pinned_head " n:ident : tactic => do
  pure (← `(tactic| rx_retention_head $(Lean.mkCIdent (Framing.normalizePinnedName n.getId))))

macro "configured_crypto " initial:term : tactic => `(tactic| first
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => view w = $initial))
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (fun w => view w = $initial))
  | (rx_retention_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (fun w => view w = $initial))
  | (rx_retention_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (fun w => view w = $initial))
  | (rx_retention_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (fun w => view w = $initial)))

theorem createInitiation_view (pid : PeerId) : SameView view (createInitiation pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first | configured_crypto initial | configured_step initial

theorem addMacToPacket_view (pid : PeerId) (msg : List UInt8) :
    SameView view (addMacToPacket pid msg) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first | configured_crypto initial | configured_step initial

theorem dstCacheGet_view (pid : PeerId) (gen : Nat) : SameView view (dstCacheGet pid gen) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' configured_step initial

theorem dstCacheSet_view (pid : PeerId) (src gen dev : Nat) : SameView view (dstCacheSet pid src gen dev) := by
  intro initial
  unfold dstCacheSet
  apply hoare_bind _ _ (getPeer_spec (fun s => s = initial) pid)
  intro p
  exact setPeer_spec (fun s => s = initial) pid _



theorem tunnelXmit_view (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView view ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact (sameWG (project := id) (loopbackSend_kernel _ _)).wp (fun s => s = initial))
    | (rx_retention_head socketPort
       exact (sameWG (project := id) (socketPort_sameStore _)).wp (fun s => s = initial))
    | configured_step initial

private theorem send4ClearSrc_view cache : SameView view (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  change Preserves (fun w => view w = initial) _
  repeat' first
    | configured_step initial

private theorem send4Finish_view e bytes ds exactRx route : SameView view (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact (tunnelXmit_view _ _ _ _ _).wp (fun t => t = initial))
    | configured_step initial

private theorem send4RouteDone_view e cache bytes ds exactRx gen fallback rt :
    SameView view (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_view _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_view _ _ _ _ _).wp (fun t => t = initial))
    | configured_step initial

private theorem send4Retry_view e cache bytes ds exactRx gen fallback srcIf rt :
    SameView view (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_view _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (ConfiguredIdentity.cacheReset _).wp (fun t => t = initial))
    | (rx_retention_head send4RouteDoneSource; exact (send4RouteDone_view _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | configured_step initial

private theorem send4Miss_view e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView view (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_view _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (ConfiguredIdentity.cacheReset _).wp (fun t => t = initial))
    | (rx_retention_head send4RetrySource; exact (send4Retry_view _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | configured_step initial

private theorem send4AfterCache_view e cache bytes ds exactRx gen saddr srcIf route :
    SameView view (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact (send4Miss_view _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_view _ _ _ _ _).wp (fun t => t = initial))
    | configured_step initial

theorem send4_view e cache bytes ds exactRx : SameView view (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_view _ _).wp (fun t => t = initial))
    | (rx_retention_head send4AfterCacheSource; exact (send4AfterCache_view _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | configured_step initial

theorem send6_view (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView view (send6 e cache bytes ds exactRx) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_view _ _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheReset; exact (ConfiguredIdentity.cacheReset _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_view _ _ _ _).wp (fun s => s = initial))
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact (tunnelXmit_view _ _ _ _ _).wp (fun s => s = initial))
    | configured_step initial

theorem sendBufferToPeer_view (pid : PeerId) (bytes : List UInt8) : SameView view (sendBufferToPeer pid bytes) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head send4; exact (send4_view _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_view _ _ _ _ _).wp (fun s => s = initial))
    | configured_step initial

theorem sendHandshakeInitiation_view (pid : PeerId) : SameView view (sendHandshakeInitiation pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createInitiation; exact (createInitiation_view _).wp (fun s => s = initial))
    | (rx_retention_head addMacToPacket; exact (addMacToPacket_view _ _).wp (fun s => s = initial))
    | (rx_retention_head timersTraversal; exact (timersTraversal_view _).wp (fun s => s = initial))
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact (timersAnyAuthenticatedPacketSent_view _).wp (fun s => s = initial))
    | (rx_retention_head timersHandshakeInitiated; exact (timersHandshakeInitiated_view _).wp (fun s => s = initial))
    | (rx_retention_head sendBufferToPeer; exact (sendBufferToPeer_view _ _).wp (fun s => s = initial))
    | configured_crypto initial
    | configured_step initial



theorem current_preserves {α : Type} (a : WG.M α)
    (identity : SameView ConfiguredIdentity.view a)
    (material : Origins.Retaining.RetainsCall a) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have hv := (ProjectedAction.iff_run_ambient _ _ _).mp identity w ambient result v ambient' hr
  constructor
  · intro s hs
    exact hi.1 s (hv.symm.trans hs)
  · apply hi.2.retain
    apply CurrentIdentity.retains_of_configured_view
    · exact (ProjectedAction.iff_run_ambient _ _ _).mp material w ambient result v ambient' hr
    · exact hv

theorem createInitiation_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (createInitiation pid) :=
  current_preserves _ (createInitiation_view pid)
    (Origins.Retaining.of_view (Origins.Retaining.createInitiation_material pid)) history

theorem sendHandshakeInitiation_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (sendHandshakeInitiation pid) :=
  current_preserves _ (sendHandshakeInitiation_view pid)
    (Origins.Retaining.of_view (Origins.Retaining.sendHandshakeInitiation_material pid)) history

/-- The final payment may erase the peer. It preserves the invariants on
normal return, without asserting exact configured-view equality or totality. -/
theorem handshakeSendWorker_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  apply preserves_bind (sendHandshakeInitiation_preserves pid history)
  intro _
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (ConfiguredIdentity.peerPut_preserves (some pid))
      w ambient result v ambient' hi.1 hr,
    hi.2.retain ((ProjectedAction.iff_run_ambient _ _ _).mp
      (CurrentIdentity.peerPut_retains (some pid)) w ambient result v ambient' hr)⟩

end Leanux.Proofs.WG.ConfiguredHandshake
