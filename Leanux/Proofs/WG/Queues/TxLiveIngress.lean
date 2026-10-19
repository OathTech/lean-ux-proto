import Leanux.Proofs.WG.Queues.TxLiveHandshake
import Leanux.Proofs.WG.Queues.TxLiveNapi

/-! The original native ingress keeps logical TX items below the packet
allocation frontier and retains the existing encryption-ring refinement.
Actual RX allocation raises the shared frontier; refusals and reference
payments retain their source order and normal/Stop domain. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveIngress
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open LiveFrontier

private theorem setRx (id : SkbId) (f : RxPacket → RxPacket) :
    Preserves Ready (setRxSkb id f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  cases hd : w.dev with
  | none => simp [setRxSkb,liftSkb_run,hd] at run
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none =>
      simp [setRxSkb,liftSkb_run,SkbStore.setRx,SkbStore.getRx,hd,hp,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      rw [Packets.setRxSkb_run w a d id p f hd hp] at run
      cases run
      simpa only [Ready,LiveFrontier.Inv,Physical,Packets.update,hd,Option.map_some,Option.some.injEq,forall_eq'] using hi

private theorem getRx (id : SkbId) : Preserves Ready (getRxSkb id) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLivePoll.«0».Leanux.Proofs.WG.Queues.TxDisposition.LivePoll.getRx) id

private theorem freeRx (id : SkbId) : Preserves Ready (freeRxSkb id) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLivePoll.«0».Leanux.Proofs.WG.Queues.TxDisposition.LivePoll.freeRx) id

macro "ingress_live_step" : tactic => `(tactic| first
  | (allocation_release_head getRxSkb; exact getRx _)
  | (allocation_release_head freeRxSkb; exact freeRx _)
  | (allocation_release_head queueDeviceWork; unfold queueDeviceWork)
  | (allocation_release_head setRxSkb; exact setRx _ _)
  | (allocation_release_head indexLookup; exact LiveFrontier.index_lookup _ _)
  | (allocation_release_head newRxSkb; exact allocator_ready (.rx _))
  | (allocation_release_head peerGet; exact peer_get _)
  | (allocation_release_head peerPut; exact peer_put _)
  | (allocation_release_head keypairGet; exact key_get _)
  | (allocation_release_head keypairPut; exact key_put _ _)
  | (allocation_release_head keypairGetNull; unfold keypairGetNull)
  | (allocation_release_head cpumaskNextOnlineFrom
     exact store_ready _ (cpumaskNextOnlineFrom_sameStore _))
  | live_socket_step)

theorem enqueue (id : SkbId) : Preserves Ready (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRx
  simp (config := {zeta := false}) only [branch]
  repeat' ingress_live_step

/-- The source's admission fallback has a literal pure IRQ callback. -/
theorem publish (id : SkbId) (state : PacketState) :
    Preserves Ready (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  unfold enqueuePerPeerRx
  simp (config := {zeta := false}) only [liftM,monadLift_self,pure_bind,invariant]
  repeat' ingress_live_step

theorem consume (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves Ready (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head enqueuePerDeviceAndPeerRx; exact enqueue _)
    | (allocation_release_head enqueuePerPeerRx; exact publish _ _)
    | ingress_live_step

theorem packet (msg : List UInt8) (src : SkbSource) :
    Preserves Ready (packetReceive msg src) := by
  unfold packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (allocation_release_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp Ready)
    | (allocation_release_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp Ready)
    | (allocation_release_head consumeData; exact consume _ _ _)
    | ingress_live_step

theorem receive (msg : List UInt8) (src : SkbSource) :
    Preserves Ready (wgReceive msg src) := by
  unfold wgReceive
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (allocation_release_head packetReceive; exact packet _ _)
    | ingress_live_step

/-- The same existing lifetime observer carries Ready on normal return. -/
theorem receive_observed (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun _ w => Ready w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveNapi.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveNapi.observed)
    _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases msg src)))
    (PublicationPoll.native_product Ready _ (receive msg src))

end Leanux.Proofs.WG.Queues.TxDisposition.LiveIngress
