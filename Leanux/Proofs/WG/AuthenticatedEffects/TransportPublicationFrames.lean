import Leanux.Proofs.WG.AuthenticatedEffects.TransportPublicationCarrier
import Leanux.Proofs.WG.Packets.PublicationPoll

/-! Concrete RX-store frames for the shared driver's packet authentication
carrier. The projection retains complete packet contents and device epoch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportPublication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

theorem Inv.sameRx (hi : Inv h w) (same : RxDisposition.nativeRxStore v = RxDisposition.nativeRxStore w) :
    Inv h v := hi.transport (fun id _ cell _ => ⟨by simpa only [same] using cell,
      congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst same)⟩)

theorem preserves_of_rx (action : WG.M α) (frame : SameView RxDisposition.nativeRxStore action)
    (h : List TransportDriver.OriginEvent) : Preserves (Inv h) action :=
  (hoare_iff_run_ambient _ _ _).mpr (fun w a x v b hi run =>
    hi.sameRx ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a x v b run))

theorem product_preserves_of_rx (action : Leanux.M α) (frame : SameView RxDisposition.rxStore action)
    (h : List TransportDriver.OriginEvent) : Preserves (fun w : World => Inv h w.wg) action :=
  (hoare_iff_run _ _ _).mpr (fun w x v hi run =>
    hi.sameRx ((ProjectedAction.iff_run _ _ _).mp frame w x v run))

theorem counterValidate_preserves (kid : KeypairId) (nonce : Nat) (h : List TransportDriver.OriginEvent) :
    Preserves (fun w : World => Inv h w.wg) (liftWG (counterValidate kid nonce)) :=
  product_preserves_of_rx _ (RxDisposition.counter_rxStore kid nonce) h

theorem peerPut_preserves (peer : Option PeerId) (h : List TransportDriver.OriginEvent) :
    Preserves (Inv h) (peerPut peer) :=
  preserves_of_rx _ (RxCredits.peerPut_rxView peer) h

theorem keypairPut_preserves (kid : Option KeypairId) (now : Bool) (h : List TransportDriver.OriginEvent) :
    Preserves (Inv h) (keypairPut kid now) :=
  preserves_of_rx _
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.keyPay) kid now).factor Prod.snd) h

theorem consumeDataDone_preserves (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (h : List TransportDriver.OriginEvent) : Preserves (Inv h) (consumeDataDone pid pkt endpoint) :=
  preserves_of_rx _
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.done_geometry) pid pkt endpoint).factor Prod.snd) h

theorem sendStagedPackets_preserves (pid : PeerId) (h : List TransportDriver.OriginEvent) :
    Preserves (Inv h) (sendStagedPackets pid) :=
  preserves_of_rx _
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.staged_geometry) pid).factor Prod.snd) h

theorem freeRxSkb_preserves (skb : SkbId) (h : List TransportDriver.OriginEvent) :
    Preserves (Inv h) (freeRxSkb skb) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  obtain ⟨cells,stamps,_,_⟩ := PublicationFrontier.freeRxSkb_frame skb w v a b run
  exact hi.transport (fun slot pkt cell _ => ⟨cells slot pkt cell,stamps slot⟩)

theorem getRxSkb_rx (skb : SkbId) : SameView RxDisposition.nativeRxStore (getRxSkb skb) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a pkt v b run
  exact congrArg _ (Packets.getRxSkb_current skb w v pkt a b run).1

theorem getPeer_rx (pid : PeerId) : SameView RxDisposition.nativeRxStore (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg _ (Peers.getPeer_current pid w v p a b run).1

theorem setPeer_rx (pid : PeerId) (peer : Peer) : SameView RxDisposition.nativeRxStore (setPeer pid peer) := by
  intro initial
  unfold setPeer modifyDev
  apply hoare_modify
  intro w hi
  simpa only [RxDisposition.nativeRxStore,Option.bind_map,Option.map_map,Function.comp_def] using hi

theorem store_rx (action : WG.M α) (frame : SameWGStore action) : SameView RxDisposition.nativeRxStore action :=
  frame.factor (fun s : WGStoreView =>
    (s.dev.map (·.ifindex),fun id : SkbId => s.dev.bind fun d => d.rxSkbs[id]?))

end Leanux.Proofs.WG.AuthenticatedEffects.TransportPublication
