import Leanux.Proofs.WG.Queues.TxRxHeadLeaves

/-! Actual receive completion keeps an old TX head through endpoint/timer
maintenance and its original staged send. All normal returns, including
rejections and empty delivery, use the same native execution. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.RxHeadCompletion
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private abbrev Ready (target : SkbId) (state : PacketState) (w : WGWorld) : Prop :=
  Packets.Inv w ∧ HeadState target state w

private theorem join_ready (target : SkbId) (state : PacketState) (g : MixedM α) (a : WG.M α)
    (erase : ErasesStatePrefix g a)
    (allocation : StatePrefixPreserves (fun h w _=>AllocationInv h w) LifetimeEvent.Safe g)
    (ready : Preserves (Ready target state) a) : Preserves (StackHead.Inv target state) a :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxRxHeadLeaves.«0».Leanux.Proofs.WG.Queues.TxDisposition.RxHeadLeaves.join)
    target state g a erase allocation
    (hoare_consequence ready (fun _ hi=>hi) (fun _ _ hi=>hi.2))

macro "rx_head_ready " target:term "," state:term : tactic => `(tactic| first
  | (allocation_release_head peekHiddenSite; unfold peekHiddenSite)
  | (allocation_release_head requireNotPending; unfold requireNotPending)
  | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) (Ready $target $state))
  | (allocation_release_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (Ready $target $state))
  | (first | allocation_release_head throw | allocation_release_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | staged_head_base $target, $state)

private theorem place (pid target : Nat) (state : PacketState) (timer : PeerTimer)
    (expires clk : UInt64) (unit : Option Nat) :
    Preserves (Ready target state) (placeOnWheel pid timer expires clk unit) := by
  unfold placeOnWheel
  material_lower
  repeat' rx_head_ready target, state

private theorem arm (pid target : Nat) (state : PacketState) (timer : PeerTimer)
    (delay : Nat) (jc : Option UInt64) : Preserves (Ready target state) (armTimer pid timer delay jc) := by
  unfold armTimer
  material_lower
  repeat' first
    | (allocation_release_head placeOnWheel; exact place _ target state _ _ _ _)
    | rx_head_ready target, state

private theorem del (pid target : Nat) (state : PacketState) (timer : PeerTimer) :
    Preserves (Ready target state) (delTimer pid timer) := by
  cases timer <;> unfold delTimer <;> repeat' rx_head_ready target, state

private theorem mod (pid target : Nat) (state : PacketState) (site : HiddenSite)
    (timer : PeerTimer) (delay : Nat) : Preserves (Ready target state) (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer modPeerTimerGuard WG.andM
  material_lower
  repeat' first
    | (allocation_release_head armTimer; exact arm _ target state _ _ _)
    | rx_head_ready target, state

private theorem complete_ready (pid target : Nat) (state : PacketState) (site : HiddenSite) :
    Preserves (Ready target state) (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  material_lower
  repeat' first
    | (allocation_release_head delTimer; exact del _ target state _)
    | rx_head_ready target, state

private theorem traversal_ready (pid target : Nat) (state : PacketState) :
    Preserves (Ready target state) (timersTraversal pid) := by
  unfold timersTraversal
  material_lower
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (allocation_release_head modPeerTimer; exact mod _ target state _ _ _)
    | rx_head_ready target, state

private theorem data_ready (pid target : Nat) (state : PacketState) :
    Preserves (Ready target state) (timersDataReceived pid) := by
  unfold timersDataReceived
  material_lower
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (allocation_release_head modPeerTimer; exact mod _ target state _ _ _)
    | rx_head_ready target, state

private theorem cache (pid target : Nat) (state : PacketState) :
    Preserves (Ready target state) (dstCacheReset pid) := by
  unfold dstCacheReset
  material_lower
  repeat' rx_head_ready target, state

private theorem endpoint_ready (pid target : Nat) (state : PacketState) (endpoint : Endpoint) :
    Preserves (Ready target state) (setPeerEndpoint pid endpoint) := by
  unfold setPeerEndpoint
  material_lower
  repeat' first
    | (allocation_release_head endpointEq
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxStackHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StackHead.store_ready)
         target state _ (endpointEq_sameStore _ _))
    | (allocation_release_head dstCacheReset; exact cache _ target state)
    | rx_head_ready target, state

private theorem lookup_ready (protocol : Nat) (bytes : List UInt8) (target : Nat) (state : PacketState) :
    Preserves (Ready target state) (lookupSrc protocol bytes) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    change wgStoreView v=wgStoreView w at borrowed
    have hd := congrArg WGStoreView.dev borrowed
    change v.dev=w.dev at hd
    simpa only [Ready,Packets.Inv,Packets.snapshot,HeadState,txPackets,hd] using hi
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    change w.dev=some d at hd
    have dev := congrArg WGStoreView.dev hv
    change v.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} at dev
    simpa only [Ready,Packets.Inv,Packets.snapshot,Packets.deviceStore,HeadState,txPackets,
      dev,hd,Option.bind_some] using hi

private theorem stats_ready (pid target : Nat) (state : PacketState) (len : Nat) :
    Preserves (Ready target state) (updateRxStats pid len) := by
  unfold updateRxStats
  repeat' rx_head_ready target, state

private theorem dishonest_ready (why : Dishonest) (target : Nat) (state : PacketState) :
    Preserves (Ready target state) (dishonest why) := by
  cases why <;> unfold dishonest <;> repeat' rx_head_ready target, state

theorem endpoint (pid target : Nat) (state : PacketState) (e : Endpoint) :
    Preserves (StackHead.Inv target state) (setPeerEndpoint pid e) :=
  join_ready target state (setPeerEndpointPrefix pid e) _ (setPeerEndpointPrefix_erases pid e)
    (AmbientContracts.drop (setPeerEndpointPrefix_spec allocationAmbient (fun _=>True) pid e))
    (endpoint_ready pid target state e)

theorem complete (pid target : Nat) (state : PacketState) (site : HiddenSite) :
    Preserves (StackHead.Inv target state) (timersHandshakeComplete pid site) :=
  join_ready target state (timersHandshakeCompletePrefix pid site) _ (timersHandshakeCompletePrefix_erases pid site)
    (AmbientContracts.drop (timersHandshakeCompletePrefix_spec allocationAmbient (fun _=>True) pid site))
    (complete_ready pid target state site)

theorem anyReceived (pid target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (timersAnyAuthenticatedPacketReceived pid) :=
  join_ready target state (timersAnyAuthenticatedPacketReceivedPrefix pid) _
    (timersAnyAuthenticatedPacketReceivedPrefix_erases pid)
    (AmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec allocationAmbient (fun _=>True) pid))
    (del pid target state _)

theorem traversal (pid target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (timersTraversal pid) :=
  join_ready target state (timersTraversalPrefix pid) _ (timersTraversalPrefix_erases pid)
    (AmbientContracts.drop (timersTraversalPrefix_spec allocationAmbient (fun _=>True) pid))
    (traversal_ready pid target state)

theorem dataReceived (pid target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (timersDataReceived pid) :=
  join_ready target state (timersDataReceivedPrefix pid) _ (timersDataReceivedPrefix_erases pid)
    (AmbientContracts.drop (timersDataReceivedPrefix_spec allocationAmbient (fun _=>True) pid))
    (data_ready pid target state)

theorem lookup (protocol : Nat) (bytes : List UInt8) (target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (lookupSrc protocol bytes) :=
  join_ready target state (lookupSrcPrefix protocol bytes) _ (lookupSrcPrefix_erases protocol bytes)
    (AmbientContracts.drop (lookupSrcPrefix_spec allocationAmbient (fun _=>True) protocol bytes))
    (lookup_ready protocol bytes target state)

theorem stats (pid target : Nat) (state : PacketState) (len : Nat) :
    Preserves (StackHead.Inv target state) (updateRxStats pid len) :=
  join_ready target state (updateRxStatsPrefix pid len) _ (updateRxStatsPrefix_erases pid len)
    (updateRxStatsPrefix_preserves allocationAmbient allocationRx pid len)
    (stats_ready pid target state len)

theorem dishonest (why : Dishonest) (target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (WG.dishonest why) :=
  join_ready target state (liftWGPrefix (WG.dishonest why)) _ (erasesStatePrefix_lift _)
    (allocationRx.dishonest why) (dishonest_ready why target state)

/-- Original RX completion, without a successful-delivery assumption. It
retains allocation validity and the saved TX head on every normal result. -/
theorem consumeDataDone (pid target : Nat) (state : PacketState) (pkt : RxPacket) (e : Endpoint) :
    Preserves (StackHead.Inv target state) (WG.consumeDataDone pid pkt e) := by
  let P := StackHead.Inv target state
  have endpoint := endpoint pid target state
  have received := fun kid=>RxHeadLeaves.received pid kid target state
  have staged := RxHeadLeaves.staged pid target state
  have fresh := RxHeadLeaves.fresh pid target state
  have complete := complete pid target state
  have anyReceived := anyReceived pid target state
  have traversal := traversal pid target state
  have data := dataReceived pid target state
  have stats := stats pid target state
  have dishonest := fun why=>dishonest why target state
  have lookup := fun protocol bytes=>lookup protocol bytes target state
  have pay := fun peer=>RxHeadLeaves.peerPut peer target state
  have ecn (protocol outer : Nat) (bytes : List UInt8) : Preserves P (inetEcnDecapsulate protocol outer bytes) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.TxStackHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StackHead.native_store)
      target state _ (inetEcnDecapsulate_sameWGStore protocol outer bytes)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  rxstack_preserves_source [WG.consumeDataDone,WG.andM,WG.orM,branch]
    using [endpoint,received,staged,fresh,complete,anyReceived,traversal,data,stats,dishonest,lookup,pay,ecn,ambient]

end Leanux.Proofs.WG.Queues.TxDisposition.RxHeadCompletion
