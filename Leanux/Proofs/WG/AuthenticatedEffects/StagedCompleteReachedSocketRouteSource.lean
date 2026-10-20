import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketCacheFrames

/-! IPv4 and IPv6 routing witnesses retain every original branch, native
route lookup, cache child and successful bind prefix before tunnel emission. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketRoute
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Prepare.Points SocketInterior

macro "socket_route_shape_step" : tactic => `(tactic| first
  | dsimp +failIfUnchanged only
  | (prepare_shape_head dstCacheGetPrefix; exact SocketCache.getShape _ _)
  | (prepare_shape_head dstCacheSetPrefix; exact SocketCache.setShape _ _ _ _)
  | (prepare_shape_head dstCacheResetMixed; exact SocketCache.resetShape _)
  | (prepare_shape_head send4ClearSrcPrefix; exact SocketCache.clear4Shape _)
  | (prepare_shape_head Six.clear; exact SocketCache.clear6Shape _)
  | (prepare_shape_head liftWGPrefix
     apply Shape.quiet
     intro initial
     change Preserves (fun w=>StagedEntry.view w=initial) _
     try simp only [branch,unsupported,invariant,getRouting]
     repeat' first
       | (rx_retention_head liftRouting; exact TimerFrames.store (liftRouting_sameWGStore _) initial)
       | (allocation_release_lift_from Net.M; exact TimerFrames.store (liftRouting_sameWGStore _) initial)
       | entry_key_step initial)
  | prepare_shape_step)

noncomputable def fourFinish (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) (route : Option Route) :
    Shape (Four.socket4FinishFront e bytes ds exactRx route) := by
  unfold Four.socket4FinishFront
  repeat' socket_route_shape_step

noncomputable def fourRoute (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (result : Except Int Route) :
    Shape (Four.socket4RouteFront e cache bytes ds exactRx gen fallback result) := by
  unfold Four.socket4RouteFront
  cases result <;> repeat' first
    | (prepare_shape_head Four.socket4FinishFront; exact fourFinish _ _ _ _ _)
    | socket_route_shape_step

noncomputable def fourRetry (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (srcIf : Nat) (result : Except Int Route) :
    Shape (Four.socket4RetryFront e cache bytes ds exactRx gen fallback srcIf result) := by
  unfold Four.socket4RetryFront
  repeat' first
    | (prepare_shape_head Four.socket4RouteFront; exact fourRoute _ _ _ _ _ _ _ _)
    | socket_route_shape_step

noncomputable def fourMiss (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (saddr srcIf : Nat) :
    Shape (Four.socket4MissFront e cache bytes ds exactRx gen fallback saddr srcIf) := by
  unfold Four.socket4MissFront
  repeat' first
    | (prepare_shape_head Four.socket4RetryFront; exact fourRetry _ _ _ _ _ _ _ _ _)
    | socket_route_shape_step

noncomputable def fourAfterCache (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) :
    Shape (Four.socket4AfterCacheFront e cache bytes ds exactRx gen saddr srcIf route) := by
  unfold Four.socket4AfterCacheFront
  repeat' first
    | (prepare_shape_head Four.socket4FinishFront; exact fourFinish _ _ _ _ _)
    | (prepare_shape_head Four.socket4MissFront; exact fourMiss _ _ _ _ _ _ _ _ _)
    | socket_route_shape_step

noncomputable def fourCached (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (slot : Option DstSlot) : Shape (match slot with
      | some s=>Four.socket4AfterCacheFront e cache bytes ds exactRx gen s.src e.srcIf (some {dev:=s.dev,src:=s.src})
      | _=>Four.socket4AfterCacheFront e cache bytes ds exactRx gen e.src e.srcIf none) := by
  cases slot <;> exact fourAfterCache _ _ _ _ _ _ _ _ _

noncomputable def four (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Shape (Four.socket4Front e cache bytes ds exactRx) := by
  unfold Four.socket4Front
  apply Shape.bind
  · socket_route_shape_step
  intro device
  apply Shape.bind
  · socket_route_shape_step
  intro noSocket
  apply boolShape noSocket
  · exact .pure _
  apply Shape.bind
  · socket_route_shape_step
  intro table
  apply Shape.bind
  · socket_route_shape_step
  intro hasCache
  apply boolShape hasCache
  · cases cache with
    | none=>
        exact .bind (SocketCache.ambientShape (AmbientM.invariant (α:=Unit) "unreachable"))
          (fun _=>fourAfterCache _ _ _ _ _ _ _ _ _)
    | some pid=>
        exact .bind (SocketCache.getShape pid table.rtGenid4)
          (fourCached e (some pid) bytes ds exactRx table.rtGenid4)
  · exact fourAfterCache _ _ _ _ _ _ _ _ _

noncomputable def sixFinish (route : Option Route) : Shape (Six.finishFront route) := by
  unfold Six.finishFront
  repeat' socket_route_shape_step

noncomputable def sixRoute (cache : Option PeerId) (gen : Nat) (fallback : Option Route) (result : Except Int Route) :
    Shape (Six.routeFront cache gen fallback result) := by
  unfold Six.routeFront
  cases result <;> repeat' first
    | (prepare_shape_head Six.finishFront; exact sixFinish _)
    | socket_route_shape_step

noncomputable def sixMiss (e : Endpoint) (cache : Option PeerId) (gen : Nat) (fallback : Option Route) (saddr : Nat) :
    Shape (Six.missFront e cache gen fallback saddr) := by
  unfold Six.missFront
  repeat' first
    | (prepare_shape_head Six.routeFront; exact sixRoute _ _ _ _)
    | socket_route_shape_step

noncomputable def sixAfterCache (e : Endpoint) (cache : Option PeerId) (gen saddr : Nat) (route : Option Route) :
    Shape (Six.afterCacheFront e cache gen saddr route) := by
  unfold Six.afterCacheFront
  repeat' first
    | (prepare_shape_head Six.finishFront; exact sixFinish _)
    | (prepare_shape_head Six.missFront; exact sixMiss _ _ _ _ _)
    | socket_route_shape_step

noncomputable def sixCached (e : Endpoint) (cache : Option PeerId) (gen : Nat) (slot : Option DstSlot) :
    Shape (match slot with
      | some s=>Six.afterCacheFront e cache gen s.src (some {dev:=s.dev,src:=s.src})
      | _=>Six.afterCacheFront e cache gen e.src none) := by
  cases slot <;> exact sixAfterCache _ _ _ _ _

noncomputable def six (e : Endpoint) (cache : Option PeerId) : Shape (Six.front e cache) := by
  unfold Six.front
  apply Shape.bind
  · socket_route_shape_step
  intro device
  apply Shape.bind
  · socket_route_shape_step
  intro noSocket
  apply boolShape noSocket
  · exact .pure _
  apply Shape.bind
  · socket_route_shape_step
  intro routing
  apply Shape.bind
  · socket_route_shape_step
  intro hasCache
  apply boolShape hasCache
  · cases cache with
    | none=>
        exact .bind (SocketCache.ambientShape (AmbientM.invariant (α:=Unit) "unreachable"))
          (fun _=>sixAfterCache _ _ _ _ _)
    | some pid=>exact .bind (SocketCache.getShape pid routing.ipv6Gen) (sixCached e (some pid) routing.ipv6Gen)
  · exact sixAfterCache _ _ _ _ _

noncomputable def canonical (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx ipv4 : Bool) : Shape (route e cache bytes ds exactRx ipv4) :=
  boolShape ipv4 _ _ (four e cache bytes ds exactRx) (six e cache)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketRoute
