import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeSocketFrames
import Leanux.Proofs.WG.AuthenticatedEffects.SocketObservation

/-! Erasure of the fixed route sources used by cookie emission. Cache and route computations remain at their original positions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CookieRoute
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open SocketInterior

macro "cookie_route_erases_step" : tactic => `(tactic| first
  | maintenance_erases_join
  | maintenance_erases_join_use
  | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_erases _)
  | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_erases _ _)
  | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_erases _ _ _ _)
  | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_erases _)
  | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
  | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
  | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
  | (maintenance_lift_head; exact erasesStatePrefix_lift _)
  | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
  | maintenance_erases_bind
  | maintenance_intro
  | maintenance_reduce
  | (maintenance_head ite; split)
  | maintenance_reduce_match
  | maintenance_match
  | maintenance_impossible_match
  | contradiction)

theorem fourFinish_erases (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) :
    ErasesStatePrefix (Four.socket4FinishFront e bytes ds exactRx route) (AuthenticatedEffects.socket4FinishFront e bytes ds exactRx route) := by
  unfold Four.socket4FinishFront AuthenticatedEffects.socket4FinishFront
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' cookie_route_erases_step

theorem fourRoute_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) :
    ErasesStatePrefix (Four.socket4RouteFront e cache bytes ds exactRx gen fallback rt) (AuthenticatedEffects.socket4RouteFront e cache bytes ds exactRx gen fallback rt) := by
  unfold Four.socket4RouteFront AuthenticatedEffects.socket4RouteFront
  try simp (config := { zeta := false }) only []
  repeat' first
    | (maintenance_head Four.socket4FinishFront; exact fourFinish_erases _ _ _ _ _)
    | cookie_route_erases_step

theorem fourRetry_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) :
    ErasesStatePrefix (Four.socket4RetryFront e cache bytes ds exactRx gen fallback srcIf rt) (AuthenticatedEffects.socket4RetryFront e cache bytes ds exactRx gen fallback srcIf rt) := by
  unfold Four.socket4RetryFront AuthenticatedEffects.socket4RetryFront
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | (maintenance_head Four.socket4FinishFront; exact fourFinish_erases _ _ _ _ _)
    | (maintenance_head Four.socket4RouteFront; exact fourRoute_erases _ _ _ _ _ _ _ _)
    | cookie_route_erases_step

theorem fourMiss_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) :
    ErasesStatePrefix (Four.socket4MissFront e cache bytes ds exactRx gen fallback saddr srcIf) (AuthenticatedEffects.socket4MissFront e cache bytes ds exactRx gen fallback saddr srcIf) := by
  unfold Four.socket4MissFront AuthenticatedEffects.socket4MissFront
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | (maintenance_head Four.socket4FinishFront; exact fourFinish_erases _ _ _ _ _)
    | (maintenance_head Four.socket4RouteFront; exact fourRoute_erases _ _ _ _ _ _ _ _)
    | (maintenance_head Four.socket4RetryFront; exact fourRetry_erases _ _ _ _ _ _ _ _ _)
    | cookie_route_erases_step

theorem fourAfter_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) :
    ErasesStatePrefix (Four.socket4AfterCacheFront e cache bytes ds exactRx gen saddr srcIf route) (AuthenticatedEffects.socket4AfterCacheFront e cache bytes ds exactRx gen saddr srcIf route) := by
  unfold Four.socket4AfterCacheFront AuthenticatedEffects.socket4AfterCacheFront
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | (maintenance_head Four.socket4FinishFront; exact fourFinish_erases _ _ _ _ _)
    | (maintenance_head Four.socket4RouteFront; exact fourRoute_erases _ _ _ _ _ _ _ _)
    | (maintenance_head Four.socket4RetryFront; exact fourRetry_erases _ _ _ _ _ _ _ _ _)
    | (maintenance_head Four.socket4MissFront; exact fourMiss_erases _ _ _ _ _ _ _ _ _)
    | cookie_route_erases_step

theorem four_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    ErasesStatePrefix (Four.socket4Front e cache bytes ds exactRx) (AuthenticatedEffects.socket4Front e cache bytes ds exactRx) := by
  unfold Four.socket4Front AuthenticatedEffects.socket4Front
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | (maintenance_head Four.socket4FinishFront; exact fourFinish_erases _ _ _ _ _)
    | (maintenance_head Four.socket4RouteFront; exact fourRoute_erases _ _ _ _ _ _ _ _)
    | (maintenance_head Four.socket4RetryFront; exact fourRetry_erases _ _ _ _ _ _ _ _ _)
    | (maintenance_head Four.socket4MissFront; exact fourMiss_erases _ _ _ _ _ _ _ _ _)
    | (maintenance_head Four.socket4AfterCacheFront; exact fourAfter_erases _ _ _ _ _ _ _ _ _)
    | cookie_route_erases_step

theorem six_erases (e : Endpoint) (cache : Option PeerId) :
    ErasesStatePrefix (Six.front e cache) (AuthenticatedEffects.socket6Front e cache) := by
  unfold Six.front Six.afterCacheFront Six.missFront Six.routeFront Six.finishFront Six.clear modifyPeerKeysPrefix AuthenticatedEffects.socket6Front
  repeat' first | rw [pure_bind] | rw [bind_assoc] | cookie_route_erases_step | split | (simp_all only [Except.ok.injEq]; subst_vars) | (rename_i impossible; exact False.elim (impossible _ rfl))

def action (args : ProtocolSocket.Args) : WG.M (Except Int Route) :=
  if args.ipv4 then AuthenticatedEffects.socket4Front args.endpoint args.cache args.bytes args.ds args.exactRx
  else AuthenticatedEffects.socket6Front args.endpoint args.cache

theorem route_erases (args : ProtocolSocket.Args) :
    ErasesStatePrefix (SocketInterior.route args.endpoint args.cache args.bytes args.ds args.exactRx args.ipv4) (action args) := by
  unfold SocketInterior.route action
  cases args.ipv4 with
  | false=>exact six_erases _ _
  | true=>exact four_erases _ _ _ _ _

inductive Point (args : ProtocolSocket.Args) : WGWorld→Ambient→WGWorld→Ambient→Prop where
  | source (point : Prepare.Points.Point
      (SocketRoute.canonical args.endpoint args.cache args.bytes args.ds args.exactRx args.ipv4)
      w a [] site v b middle remaining) : Point args w a v b

theorem Point.remaining (point : Point args w a v b) :
    ∃remaining : WG.M (Except Int Route),((action args).run w).run a=(remaining.run v).run b := by
  cases point with
  | source point=>
    rename_i site middle remaining
    refine ⟨NativeSocket.unobserve remaining middle,?_⟩
    rw [←route_erases args w a []]
    exact congrArg Prod.fst point.run

theorem Point.observed_remaining {E : Type} {w : World}
    (point : Point args w.wg w.ambient v b) (h : List E) :
    ∃remaining : PrefixM E (Except Int Route),runPrefix (liftWGObserver (liftWGPrefix (action args))) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CookieRoute
