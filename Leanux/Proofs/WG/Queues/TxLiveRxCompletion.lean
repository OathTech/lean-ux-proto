import Leanux.Proofs.WG.Queues.TxLiveStack
import Leanux.Proofs.WG.Queues.TxLiveTimers
import Leanux.Proofs.WG.Queues.TxRxHeadCompletion

/-! Actual RX completion retains numeric bounds on logical live TX items and
the existing physical ring witness. Native send uses its checked staged source;
no whole-action frame or packet residency assumption is introduced. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveRx
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open LiveFrontier

macro "rx_live_step" : tactic => `(tactic| first
  | (allocation_release_head peekHiddenSite; unfold peekHiddenSite)
  | (allocation_release_head requireNotPending; unfold requireNotPending)
  | (allocation_release_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp Ready)
  | (first | allocation_release_head throw | allocation_release_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | live_send_step)

private theorem cache (pid : Nat) :
    Preserves Ready (dstCacheReset pid) := by
  unfold dstCacheReset
  material_lower
  repeat' rx_live_step

private theorem endpoint_ready (pid : Nat) (endpoint : Endpoint) :
    Preserves Ready (setPeerEndpoint pid endpoint) := by
  unfold setPeerEndpoint
  material_lower
  repeat' first
    | (allocation_release_head endpointEq
       exact LiveFrontier.store_ready _ (endpointEq_sameStore _ _))
    | (allocation_release_head dstCacheReset; exact cache _)
    | rx_live_step

private theorem lookup_ready (family : Nat) (addr : List UInt8) : Preserves Ready (lookupSrc family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none=>
    change wgStoreView v=wgStoreView w at borrowed
    have dev : v.dev=w.dev := congrArg WGStoreView.dev borrowed
    simpa only [Ready,LiveFrontier.Inv,Physical,dev] using hi
  | some pid=>
    obtain ⟨d,p,device,_,_,same⟩ := borrowed
    change w.dev=some d at device
    have endpoint := congrArg WGStoreView.dev same
    change v.dev=some {d with peers:=d.peers.insert pid {p with refcount:=p.refcount+1}} at endpoint
    simpa only [Ready,LiveFrontier.Inv,Physical,device,endpoint,Option.some.injEq,forall_eq'] using hi

private theorem stats_ready (pid : Nat) (len : Nat) :
    Preserves Ready (updateRxStats pid len) := by
  unfold updateRxStats
  repeat' rx_live_step

private theorem dishonest_ready (why : Dishonest) :
    Preserves Ready (dishonest why) := by
  cases why <;> unfold dishonest <;> repeat' rx_live_step

theorem received (pid kid : Nat) : Preserves Ready (receivedWithKeypair pid kid) := by
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head keypairPut; exact key_put _ _)
    | rx_live_step

theorem fresh (pid : PeerId) : Preserves Ready (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head sendQueuedHandshakeInitiation; exact queued _ _)
    | rx_live_step

/-- All normal receive-completion results retain the live-ring frontier,
including rejection and empty-payload paths and actual optional peer deletion. -/
theorem consume (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Preserves Ready (WG.consumeDataDone pid pkt e) := by
  have endpoint := endpoint_ready pid
  have received := received pid
  have staged := send pid
  have fresh := fresh pid
  have complete := handshake_complete pid
  have anyReceived := authenticated_received pid
  have traversal := LiveFrontier.traversal pid
  have data := data_received pid
  have stats := stats_ready pid
  have dishonest := dishonest_ready
  have lookup := lookup_ready
  have pay := peer_put
  have ecn (protocol outer : Nat) (bytes : List UInt8) : Preserves Ready (inetEcnDecapsulate protocol outer bytes) :=
    store_ready _ (inetEcnDecapsulate_sameWGStore protocol outer bytes)
  have ambient {α : Type} (a : AmbientM α) : Preserves Ready (monadLift a : WG.M α) := hoare_liftAmbient a Ready
  rxstack_preserves_source [WG.consumeDataDone,WG.andM,WG.orM,branch]
    using [endpoint,received,staged,fresh,complete,anyReceived,traversal,data,stats,dishonest,lookup,pay,ecn,ambient]

end Leanux.Proofs.WG.Queues.TxDisposition.LiveRx
