import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketRouteFrames

/-! The socket front expands the demanded saved-peer scan and tunnel
preparation, stopping immediately before the sole datagram append. Every
leaf is an original read, branch, routing call or projection-preserving write. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketFront
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Prepare.Points SocketInterior

theorem savedRead_source (pid : PeerId) (p : Peer) : savedPeerRead pid p=
    receiptWGObserved (pure ()) (fun _=>LifetimeEvent.peer (.read pid p.internalId)) := by
  funext w a h
  rfl

noncomputable def savedRead (pid : PeerId) (p : Peer) : Shape (savedPeerRead pid p) := by
  rw [savedRead_source]
  exact .receipt (.pure ()) _

noncomputable def savedAny (test : Peer → Bool) (peers : List (PeerId × Peer)) : Shape (savedPeerAny test peers) := by
  induction peers with
  | nil=>exact .pure false
  | cons pair rest ih=>
      exact .bind (savedRead pair.1 pair.2) (fun _=>boolShape (test pair.2) _ _ (.pure true) ih)

noncomputable def softirq : Shape loopbackSoftirqPrefix := by
  unfold loopbackSoftirqPrefix
  repeat' first
    | (prepare_shape_head savedPeerAny; exact savedAny _ _)
    | (prepare_shape_head liftWGPrefix
       apply Shape.metadata
       repeat' first
         | (metadata_source_head loopbackFinish; exact PeerMetadata.loopbackFinishShape)
         | socket_metadata_step)
    | socket_route_shape_step

noncomputable def loopback (sites : List HiddenSite) (raised : Bool) : Shape (loopbackSendPrefix sites raised) := by
  unfold loopbackSendPrefix
  apply Shape.bind (SocketCache.ambientShape (AmbientM.skipCut sites))
  intro ignored
  apply boolShape raised
  · exact .bind (.metadata _ PeerMetadata.loopbackRaiseShape) (fun _=>softirq)
  · exact .pure ()

noncomputable def tunnel (e : Endpoint) (bytes : List UInt8) (r : Route) (exactRx : Bool) :
    Shape (tunnelFront e bytes r exactRx) := by
  unfold tunnelFront
  repeat' first
    | (prepare_shape_head loopbackSendPrefix; exact loopback _ _)
    | (prepare_shape_head liftWGPrefix
       apply Shape.metadata
       repeat' first
         | (metadata_source_head socketPort; exact PeerMetadata.socketPortShape _)
         | socket_metadata_step)
    | socket_route_shape_step

noncomputable def afterRouteShape (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)
    (result : Except Int Route) : Shape (afterRoute e bytes ds exactRx result) := by
  cases result with
  | error code=>exact .pure (Except.error (α:=SentDatagram) code)
  | ok route=>exact .bind (tunnel e bytes route exactRx) (fun sport=>.pure (Except.ok (ε:=Int) (datagram e bytes ds route sport)))

noncomputable def canonical (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx ipv4 : Bool) : Shape (beforeAppend e cache bytes ds exactRx ipv4) :=
  .bind (SocketRoute.canonical e cache bytes ds exactRx ipv4) (afterRouteShape e bytes ds exactRx)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketFront
