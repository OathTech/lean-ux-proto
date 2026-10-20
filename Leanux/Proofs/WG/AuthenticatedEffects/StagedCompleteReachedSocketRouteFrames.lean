import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketRouteSource

/-! Routing and cache preparation preserve the incoming packet account.
Frames follow fixed successful prefixes and derive each saved write from
its own peer getter. No route result or family is assumed successful. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketRoute
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation Prepare.Points SocketInterior

elab "socket_framed_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Framed do Lean.throwError "not a source frame"
  let args := target.getAppArgs
  let shape := args[args.size-4]!.consumeMData.headBeta
  let .const actual _ := shape.getAppFn | Lean.throwError "not a named source witness"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source witness"

macro "socket_cache_frame_step" : tactic => `(tactic| first
  | (socket_framed_head SocketCache.getShape; exact SocketCache.get_framed _ _ _)
  | (socket_framed_head SocketCache.setShape; exact SocketCache.set_framed _ _ _ _ _)
  | (socket_framed_head SocketCache.resetShape; exact SocketCache.reset_framed _ _)
  | (socket_framed_head SocketCache.clear4Shape; exact SocketCache.clear4_framed _ _)
  | (socket_framed_head SocketCache.clear6Shape; exact SocketCache.clear6_framed _ _)
  | prepare_direct_frame_step)

theorem fourFinish_framed (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)
    (route : Option Route) (h : List LifetimeEvent) : Framed (fourFinish e bytes ds exactRx route) w a h := by
  cases route <;> unfold fourFinish
  all_goals repeat' socket_cache_frame_step

theorem fourRoute_framed (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (result : Except Int Route) (h : List LifetimeEvent) :
    Framed (fourRoute e cache bytes ds exactRx gen fallback result) w a h := by
  cases result <;> unfold fourRoute
  all_goals repeat' first
    | (socket_framed_head fourFinish; exact fourFinish_framed _ _ _ _ _ _)
    | socket_cache_frame_step

theorem fourRetry_framed (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (srcIf : Nat) (result : Except Int Route) (h : List LifetimeEvent) :
    Framed (fourRetry e cache bytes ds exactRx gen fallback srcIf result) w a h := by
  unfold fourRetry
  repeat' first
    | (socket_framed_head fourRoute; exact fourRoute_framed _ _ _ _ _ _ _ _ _)
    | socket_cache_frame_step

theorem fourMiss_framed (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (saddr srcIf : Nat) (h : List LifetimeEvent) :
    Framed (fourMiss e cache bytes ds exactRx gen fallback saddr srcIf) w a h := by
  unfold fourMiss
  repeat' first
    | (socket_framed_head fourRetry; exact fourRetry_framed _ _ _ _ _ _ _ _ _ _)
    | socket_cache_frame_step

theorem fourAfterCache_framed (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) (h : List LifetimeEvent) :
    Framed (fourAfterCache e cache bytes ds exactRx gen saddr srcIf route) w a h := by
  unfold fourAfterCache
  repeat' first
    | (socket_framed_head fourFinish; exact fourFinish_framed _ _ _ _ _ _)
    | (socket_framed_head fourMiss; exact fourMiss_framed _ _ _ _ _ _ _ _ _ _)
    | socket_cache_frame_step

theorem fourCached_framed (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (slot : Option DstSlot) (h : List LifetimeEvent) :
    Framed (fourCached e cache bytes ds exactRx gen slot) w a h := by
  cases slot <;> exact fourAfterCache_framed _ _ _ _ _ _ _ _ _ _

theorem four_framed (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)
    (h : List LifetimeEvent) : Framed (four e cache bytes ds exactRx) w a h := by
  cases cache <;> unfold four
  all_goals repeat' first
    | (socket_framed_head fourCached; exact fourCached_framed _ _ _ _ _ _ _ _)
    | (socket_framed_head fourAfterCache; exact fourAfterCache_framed _ _ _ _ _ _ _ _ _ _)
    | socket_cache_frame_step

theorem sixFinish_framed (route : Option Route) (h : List LifetimeEvent) : Framed (sixFinish route) w a h := by
  cases route <;> unfold sixFinish
  all_goals repeat' socket_cache_frame_step

theorem sixRoute_framed (cache : Option PeerId) (gen : Nat) (fallback : Option Route) (result : Except Int Route)
    (h : List LifetimeEvent) : Framed (sixRoute cache gen fallback result) w a h := by
  cases result <;> unfold sixRoute
  all_goals repeat' first
    | (socket_framed_head sixFinish; exact sixFinish_framed _ _)
    | socket_cache_frame_step

theorem sixMiss_framed (e : Endpoint) (cache : Option PeerId) (gen : Nat) (fallback : Option Route) (saddr : Nat)
    (h : List LifetimeEvent) : Framed (sixMiss e cache gen fallback saddr) w a h := by
  unfold sixMiss
  repeat' first
    | (socket_framed_head sixRoute; exact sixRoute_framed _ _ _ _ _)
    | socket_cache_frame_step

theorem sixAfterCache_framed (e : Endpoint) (cache : Option PeerId) (gen saddr : Nat) (route : Option Route)
    (h : List LifetimeEvent) : Framed (sixAfterCache e cache gen saddr route) w a h := by
  unfold sixAfterCache
  repeat' first
    | (socket_framed_head sixFinish; exact sixFinish_framed _ _)
    | (socket_framed_head sixMiss; exact sixMiss_framed _ _ _ _ _ _)
    | socket_cache_frame_step

theorem sixCached_framed (e : Endpoint) (cache : Option PeerId) (gen : Nat) (slot : Option DstSlot)
    (h : List LifetimeEvent) : Framed (sixCached e cache gen slot) w a h := by
  cases slot <;> exact sixAfterCache_framed _ _ _ _ _ _

theorem six_framed (e : Endpoint) (cache : Option PeerId) (h : List LifetimeEvent) : Framed (six e cache) w a h := by
  cases cache <;> unfold six
  all_goals repeat' first
    | (socket_framed_head sixCached; exact sixCached_framed _ _ _ _ _)
    | (socket_framed_head sixAfterCache; exact sixAfterCache_framed _ _ _ _ _ _)
    | socket_cache_frame_step

theorem canonical_framed (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx ipv4 : Bool)
    (h : List LifetimeEvent) : Framed (canonical e cache bytes ds exactRx ipv4) w a h :=
  boolShape_framed _ _ _ h (four_framed _ _ _ _ _ _) (six_framed _ _ _)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketRoute
