import Leanux.Proofs.WG.Lifetimes.SocketSend

/-! The IPv4 socket path in explicit tail stages. The source stages only
factor the original control flow; the observer stages retain every access and
the original nested WG/Ambient result or Stop. `fallback` keeps the entry route even in
the route-error branch's false fallthrough. No endpoint-validity premise is
used. -/
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def send4ClearSrcSource (cache : Option PeerId) : WG.M Unit := do
  if let some pid := cache then
    let p ← getPeer pid
    setPeer pid {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}}

def send4FinishSource (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) : WG.M Int := do
  let some r := route | invariant "send4 without a route"
  liftRouting (Net.Fib.inSocketNs (Net.neighbourClassify r.dev))
  (pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx
  return 0

def send4RouteDoneSource (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) : WG.M Int := do
  let mut route := fallback
  match rt with
  | .error err =>
    if ← branch .send4RouteErr true then return err
  | .ok r =>
    _ ← branch .send4RouteErr false
    if ← branch .send4CacheSet cache.isSome then dstCacheSet cache.get! r.src gen r.dev
    route := some r
  send4FinishSource e bytes ds exactRx route

def send4RetrySource (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) : WG.M Int := do
  let mut rt := rt
  let mismatch := srcIf != 0 && (match rt with
    | .error err => err == -EINVAL
    | .ok r => r.dev != srcIf)
  if ← branch .send4SrcIfMismatch mismatch then
    send4ClearSrcSource cache
    if ← branch .send4ResetB cache.isSome then dstCacheReset cache.get!
    if ← branch .send4PutRt (match rt with | .ok _ => true | .error _ => false) then pure ()
    rt ← liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 0 e.addr))
  send4RouteDoneSource e cache bytes ds exactRx gen fallback rt

def send4MissSource (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) : WG.M Int := do
  let mut saddr := saddr
  let mut srcIf := srcIf
  let w ← (getRouting : WG.M Net.Routing)
  let confirmed := saddr == 0 || saddr == LOOPBACK4 || w.addrs4.contains saddr
  if ← branch .send4SrcNotLocal !confirmed then
    send4ClearSrcSource cache
    saddr := 0; srcIf := 0
    if ← branch .send4ResetA cache.isSome then dstCacheReset cache.get!
  let rt ← liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 saddr e.addr))
  send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt

def send4AfterCacheSource (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) : WG.M Int := do
  if ← branch .send4CacheMiss route.isNone then
    send4MissSource e cache bytes ds exactRx gen route saddr srcIf
  else send4FinishSource e bytes ds exactRx route

def send4Source (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) : WG.M Int := do
  let d ← getDev
  if ← branch .send4SockNull d.sock4.isNone then return -ENONET
  let gen := (← liftRouting (Net.Fib.inSocketNs Net.Fib.getTable)).rtGenid4.toNat   -- the word's value, as `send4` reads it
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← branch .send4HasCache cache.isSome then
    let some pid := cache | invariant "unreachable"
    if let some s ← dstCacheGet pid gen then
      route := some {dev := s.dev, src := s.src}; saddr := s.src
  send4AfterCacheSource e cache bytes ds exactRx gen saddr e.srcIf route

theorem send4Source_eq (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    send4Source e cache bytes ds exactRx = send4 e cache bytes ds exactRx := by
  unfold send4Source send4 send4AfterCacheSource send4MissSource send4RetrySource
    send4RouteDoneSource send4FinishSource send4ClearSrcSource
  repeat' first
    | rfl
    | (congr 1)
    | (funext x)
    | split

def send4ClearSrcPrefix (cache : Option PeerId) : MixedM Unit := do
  if let some pid := cache then
    modifyPeerKeysPrefix pid fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}}

def send4FinishPrefix (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) : MixedM Int := do
  let some r := route | liftWGPrefix (invariant "send4 without a route")
  liftWGPrefix (liftRouting (Net.Fib.inSocketNs (Net.neighbourClassify r.dev)))
  tunnelXmitPrefix e bytes ds r exactRx
  return 0

def send4RouteDonePrefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) : MixedM Int := do
  let mut route := fallback
  match rt with
  | .error err =>
    if ← liftWGPrefix (branch .send4RouteErr true) then return err
  | .ok r =>
    _ ← liftWGPrefix (branch .send4RouteErr false)
    if ← liftWGPrefix (branch .send4CacheSet cache.isSome) then dstCacheSetPrefix cache.get! r.src gen r.dev
    route := some r
  send4FinishPrefix e bytes ds exactRx route

def send4RetryPrefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) : MixedM Int := do
  let mut rt := rt
  let mismatch := srcIf != 0 && (match rt with
    | .error err => err == -EINVAL
    | .ok r => r.dev != srcIf)
  if ← liftWGPrefix (branch .send4SrcIfMismatch mismatch) then
    send4ClearSrcPrefix cache
    if ← liftWGPrefix (branch .send4ResetB cache.isSome) then dstCacheResetMixed cache.get!
    if ← liftWGPrefix (branch .send4PutRt (match rt with | .ok _ => true | .error _ => false)) then pure ()
    rt ← liftWGPrefix (liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 0 e.addr)))
  send4RouteDonePrefix e cache bytes ds exactRx gen fallback rt

def send4MissPrefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) : MixedM Int := do
  let mut saddr := saddr
  let mut srcIf := srcIf
  let w ← liftWGPrefix (getRouting : WG.M Net.Routing)
  let confirmed := saddr == 0 || saddr == LOOPBACK4 || w.addrs4.contains saddr
  if ← liftWGPrefix (branch .send4SrcNotLocal !confirmed) then
    send4ClearSrcPrefix cache
    saddr := 0; srcIf := 0
    if ← liftWGPrefix (branch .send4ResetA cache.isSome) then dstCacheResetMixed cache.get!
  let rt ← liftWGPrefix (liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 saddr e.addr)))
  send4RetryPrefix e cache bytes ds exactRx gen fallback srcIf rt

def send4AfterCachePrefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) : MixedM Int := do
  if ← liftWGPrefix (branch .send4CacheMiss route.isNone) then
    send4MissPrefix e cache bytes ds exactRx gen route saddr srcIf
  else send4FinishPrefix e bytes ds exactRx route

def send4Prefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) : MixedM Int := do
  let d ← liftWGPrefix getDev
  if ← liftWGPrefix (branch .send4SockNull d.sock4.isNone) then return -ENONET
  let gen := (← liftWGPrefix (liftRouting (Net.Fib.inSocketNs Net.Fib.getTable))).rtGenid4.toNat
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← liftWGPrefix (branch .send4HasCache cache.isSome) then
    let some pid := cache | liftWGPrefix (invariant "unreachable")
    if let some s ← dstCacheGetPrefix pid gen then
      route := some {dev := s.dev, src := s.src}; saddr := s.src
  send4AfterCachePrefix e cache bytes ds exactRx gen saddr e.srcIf route

theorem send4ClearSrcPrefix_erases (cache : Option PeerId) :
    ErasesStatePrefix (send4ClearSrcPrefix cache) (send4ClearSrcSource cache) := by
  unfold send4ClearSrcPrefix send4ClearSrcSource
  unfold modifyPeerKeysPrefix
  try simp (config := { zeta := false }) only []
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_erases _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_erases _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_erases _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_erases _)
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
    | contradiction

theorem send4FinishPrefix_erases (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) :
    ErasesStatePrefix (send4FinishPrefix e bytes ds exactRx route) (send4FinishSource e bytes ds exactRx route) := by
  unfold send4FinishPrefix send4FinishSource
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_erases _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_erases _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_erases _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_erases _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_erases _)
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
    | contradiction

theorem send4RouteDonePrefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) :
    ErasesStatePrefix (send4RouteDonePrefix e cache bytes ds exactRx gen fallback rt) (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  unfold send4RouteDonePrefix send4RouteDoneSource
  try simp (config := { zeta := false }) only []
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_erases _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_erases _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_erases _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_erases _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_erases _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_erases _)
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
    | contradiction

theorem send4RetryPrefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) :
    ErasesStatePrefix (send4RetryPrefix e cache bytes ds exactRx gen fallback srcIf rt) (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  unfold send4RetryPrefix send4RetrySource
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_erases _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_erases _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_erases _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_erases _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_erases _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_erases _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_erases _)
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
    | contradiction

theorem send4MissPrefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) :
    ErasesStatePrefix (send4MissPrefix e cache bytes ds exactRx gen fallback saddr srcIf) (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  unfold send4MissPrefix send4MissSource
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_erases _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_erases _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_erases _ _ _ _ _ _ _ _)
    | (maintenance_head send4RetryPrefix; exact send4RetryPrefix_erases _ _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_erases _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_erases _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_erases _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_erases _)
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
    | contradiction

theorem send4AfterCachePrefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) :
    ErasesStatePrefix (send4AfterCachePrefix e cache bytes ds exactRx gen saddr srcIf route) (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  unfold send4AfterCachePrefix send4AfterCacheSource
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_erases _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_erases _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_erases _ _ _ _ _ _ _ _)
    | (maintenance_head send4RetryPrefix; exact send4RetryPrefix_erases _ _ _ _ _ _ _ _ _)
    | (maintenance_head send4MissPrefix; exact send4MissPrefix_erases _ _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_erases _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_erases _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_erases _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_erases _)
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
    | contradiction

theorem send4Prefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    ErasesStatePrefix (send4Prefix e cache bytes ds exactRx) (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  unfold send4Prefix send4Source
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_erases _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_erases _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_erases _ _ _ _ _ _ _ _)
    | (maintenance_head send4RetryPrefix; exact send4RetryPrefix_erases _ _ _ _ _ _ _ _ _)
    | (maintenance_head send4MissPrefix; exact send4MissPrefix_erases _ _ _ _ _ _ _ _ _)
    | (maintenance_head send4AfterCachePrefix; exact send4AfterCachePrefix_erases _ _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_erases _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_erases _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_erases _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_erases _)
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
    | contradiction

theorem send4ClearSrcPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (cache : Option PeerId) :
    AmbientSpec I P (send4ClearSrcPrefix cache) (fun _ => P) := by
  unfold send4ClearSrcPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.store P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.store P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.store P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4FinishPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) :
    AmbientSpec I P (send4FinishPrefix e bytes ds exactRx route) (fun _ => P) := by
  unfold send4FinishPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec c P _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.store P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.store P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.store P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4RouteDonePrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) :
    AmbientSpec I P (send4RouteDonePrefix e cache bytes ds exactRx gen fallback rt) (fun _ => P) := by
  unfold send4RouteDonePrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec c P _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.store P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.store P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.store P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4RetryPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) :
    AmbientSpec I P (send4RetryPrefix e cache bytes ds exactRx gen fallback srcIf rt) (fun _ => P) := by
  unfold send4RetryPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec c P _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_spec c sc P _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.store P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.store P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.store P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4MissPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) :
    AmbientSpec I P (send4MissPrefix e cache bytes ds exactRx gen fallback saddr srcIf) (fun _ => P) := by
  unfold send4MissPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec c P _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_spec c sc P _ _ _ _ _ _ _ _)
    | (maintenance_head send4RetryPrefix; exact send4RetryPrefix_spec c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.store P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.store P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.store P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4AfterCachePrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) :
    AmbientSpec I P (send4AfterCachePrefix e cache bytes ds exactRx gen saddr srcIf route) (fun _ => P) := by
  unfold send4AfterCachePrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec c P _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_spec c sc P _ _ _ _ _ _ _ _)
    | (maintenance_head send4RetryPrefix; exact send4RetryPrefix_spec c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head send4MissPrefix; exact send4MissPrefix_spec c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.store P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.store P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.store P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4Prefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    AmbientSpec I P (send4Prefix e cache bytes ds exactRx) (fun _ => P) := by
  unfold send4Prefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec c P _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_spec c sc P _ _ _ _ _ _ _ _)
    | (maintenance_head send4RetryPrefix; exact send4RetryPrefix_spec c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head send4MissPrefix; exact send4MissPrefix_spec c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head send4AfterCachePrefix; exact send4AfterCachePrefix_spec c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.store P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.store P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.store P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

/-- The clear-source/reset segment used by either IPv4 miss arm retains the
endpoint read and write when the following reset-clock record fails. Premises
name original getter, setter and clock executions, not observer histories. -/
theorem send4_clear_reset_clock_failure (pid : PeerId) (w v : WGWorld) (ambient ambient' : Ambient) (p : Peer)
    (h : List LifetimeEvent) (err : Stop)
    (hd : w.dev.isSome = true)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient))
    (hw : ((setPeer pid {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}}).run w).run ambient = .ok (((), v), ambient'))
    (ha : ambient'.armRecords = true) (hc : v.dstCacheRecords = true)
    (hf : ((hiddenJiffies .dstCacheResetTs : WG.M UInt64).run v).run ambient' = .error err) :
    runStatePrefix (do send4ClearSrcPrefix (some pid); dstCacheResetMixed pid) w ambient h =
      (.error err, h ++ [.peer (.read pid p.internalId), .peer (.write pid p.internalId)]) := by
  simp [send4ClearSrcPrefix, modifyPeerKeysPrefix, dstCacheResetMixed,
    runStatePrefix_bind, runStatePrefix_lift, liftWGPrefix, getPeerMixed_run, setPeerMixed_run, hd, hp, hw, ha, hc, hf,
    getAmbient, StateT.run_pure,
    List.append_assoc]

theorem send4ClearSrcPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (cache : Option PeerId) :
    ProductAmbientSpec I P (liftWGObserver (send4ClearSrcPrefix cache)) (fun _ => P) := by
  unfold send4ClearSrcPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec_product c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec_product c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec_product c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.nativeStore P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.nativeStore P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.nativeStore P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4FinishPrefix_spec_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) :
    ProductAmbientSpec I P (liftWGObserver (send4FinishPrefix e bytes ds exactRx route)) (fun _ => P) := by
  unfold send4FinishPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec_product c P _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec_product c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec_product c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec_product c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.nativeStore P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.nativeStore P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.nativeStore P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4RouteDonePrefix_spec_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) :
    ProductAmbientSpec I P (liftWGObserver (send4RouteDonePrefix e cache bytes ds exactRx gen fallback rt)) (fun _ => P) := by
  unfold send4RouteDonePrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec_product c P _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec_product c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec_product c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec_product c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.nativeStore P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.nativeStore P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.nativeStore P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4RetryPrefix_spec_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) :
    ProductAmbientSpec I P (liftWGObserver (send4RetryPrefix e cache bytes ds exactRx gen fallback srcIf rt)) (fun _ => P) := by
  unfold send4RetryPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec_product c P _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_spec_product c sc P _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec_product c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec_product c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec_product c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.nativeStore P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.nativeStore P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.nativeStore P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4MissPrefix_spec_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) :
    ProductAmbientSpec I P (liftWGObserver (send4MissPrefix e cache bytes ds exactRx gen fallback saddr srcIf)) (fun _ => P) := by
  unfold send4MissPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec_product c P _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_spec_product c sc P _ _ _ _ _ _ _ _)
    | (maintenance_head send4RetryPrefix; exact send4RetryPrefix_spec_product c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec_product c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec_product c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec_product c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.nativeStore P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.nativeStore P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.nativeStore P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4AfterCachePrefix_spec_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) :
    ProductAmbientSpec I P (liftWGObserver (send4AfterCachePrefix e cache bytes ds exactRx gen saddr srcIf route)) (fun _ => P) := by
  unfold send4AfterCachePrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec_product c P _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_spec_product c sc P _ _ _ _ _ _ _ _)
    | (maintenance_head send4RetryPrefix; exact send4RetryPrefix_spec_product c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head send4MissPrefix; exact send4MissPrefix_spec_product c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec_product c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec_product c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec_product c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.nativeStore P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.nativeStore P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.nativeStore P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send4Prefix_spec_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    ProductAmbientSpec I P (liftWGObserver (send4Prefix e cache bytes ds exactRx)) (fun _ => P) := by
  unfold send4Prefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head send4ClearSrcPrefix; exact send4ClearSrcPrefix_spec_product c P _)
    | (maintenance_head send4FinishPrefix; exact send4FinishPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head send4RouteDonePrefix; exact send4RouteDonePrefix_spec_product c sc P _ _ _ _ _ _ _ _)
    | (maintenance_head send4RetryPrefix; exact send4RetryPrefix_spec_product c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head send4MissPrefix; exact send4MissPrefix_spec_product c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head send4AfterCachePrefix; exact send4AfterCachePrefix_spec_product c sc P _ _ _ _ _ _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec_product c P _ _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec_product c P _ _ _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec_product c P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head getDev; exact c.nativeStore P _
        getDev_sameWGStore)
    | (maintenance_lift_action_head liftRouting; exact c.nativeStore P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact c.nativeStore P _
        (by
          intro initial
          unfold getRouting
          exact hoare_liftRouting
            ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
            (fun w => wgStoreView w = initial) (fun _ _ hi => hi)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

end Leanux.Proofs.WG.Lifetimes
