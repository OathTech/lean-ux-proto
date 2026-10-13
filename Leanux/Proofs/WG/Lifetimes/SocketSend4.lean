import Leanux.Proofs.WG.Lifetimes.SocketSend

/-! The IPv4 socket path in explicit tail stages. The source stages only
factor the original control flow; the observer stages retain every access and
the original result/World or Stop. `fallback` keeps the entry route even in
the route-error branch's false fallthrough. No endpoint-validity premise is
used. -/
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def send4ClearSrcSource (cache : Option PeerId) : M Unit := do
  if let some pid := cache then
    let p ← getPeer pid
    setPeer pid {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}}

def send4FinishSource (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) : M Int := do
  let some r := route | invariant "send4 without a route"
  (pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx
  return 0

def send4RouteDoneSource (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) : M Int := do
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
    (srcIf : Nat) (rt : Except Int Route) : M Int := do
  let mut rt := rt
  let mismatch := srcIf != 0 && (match rt with
    | .error err => err == -EINVAL
    | .ok r => r.dev != srcIf)
  if ← branch .send4SrcIfMismatch mismatch then
    send4ClearSrcSource cache
    if ← branch .send4ResetB cache.isSome then dstCacheReset cache.get!
    if ← branch .send4PutRt (match rt with | .ok _ => true | .error _ => false) then pure ()
    rt ← routeLookup 4 0 e.addr
  send4RouteDoneSource e cache bytes ds exactRx gen fallback rt

def send4MissSource (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) : M Int := do
  let mut saddr := saddr
  let mut srcIf := srcIf
  let w ← get
  let confirmed := saddr == 0 || saddr == LOOPBACK4 || w.addrs4.contains saddr
  if ← branch .send4SrcNotLocal !confirmed then
    send4ClearSrcSource cache
    saddr := 0; srcIf := 0
    if ← branch .send4ResetA cache.isSome then dstCacheReset cache.get!
  let rt ← routeLookup 4 saddr e.addr
  send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt

def send4AfterCacheSource (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) : M Int := do
  if ← branch .send4CacheMiss route.isNone then
    send4MissSource e cache bytes ds exactRx gen route saddr srcIf
  else send4FinishSource e bytes ds exactRx route

def send4Source (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) : M Int := do
  let d ← getDev
  if ← branch .send4SockNull d.sock4.isNone then return -ENONET
  let gen := (← get).ipv4Gen
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
  let some r := route | liftPrefix (invariant "send4 without a route")
  tunnelXmitPrefix e bytes ds r exactRx
  return 0

def send4RouteDonePrefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) : MixedM Int := do
  let mut route := fallback
  match rt with
  | .error err =>
    if ← liftPrefix (branch .send4RouteErr true) then return err
  | .ok r =>
    _ ← liftPrefix (branch .send4RouteErr false)
    if ← liftPrefix (branch .send4CacheSet cache.isSome) then dstCacheSetPrefix cache.get! r.src gen r.dev
    route := some r
  send4FinishPrefix e bytes ds exactRx route

def send4RetryPrefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) : MixedM Int := do
  let mut rt := rt
  let mismatch := srcIf != 0 && (match rt with
    | .error err => err == -EINVAL
    | .ok r => r.dev != srcIf)
  if ← liftPrefix (branch .send4SrcIfMismatch mismatch) then
    send4ClearSrcPrefix cache
    if ← liftPrefix (branch .send4ResetB cache.isSome) then dstCacheResetMixed cache.get!
    if ← liftPrefix (branch .send4PutRt (match rt with | .ok _ => true | .error _ => false)) then pure ()
    rt ← liftPrefix (routeLookup 4 0 e.addr)
  send4RouteDonePrefix e cache bytes ds exactRx gen fallback rt

def send4MissPrefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) : MixedM Int := do
  let mut saddr := saddr
  let mut srcIf := srcIf
  let w ← liftPrefix (get : M World)
  let confirmed := saddr == 0 || saddr == LOOPBACK4 || w.addrs4.contains saddr
  if ← liftPrefix (branch .send4SrcNotLocal !confirmed) then
    send4ClearSrcPrefix cache
    saddr := 0; srcIf := 0
    if ← liftPrefix (branch .send4ResetA cache.isSome) then dstCacheResetMixed cache.get!
  let rt ← liftPrefix (routeLookup 4 saddr e.addr)
  send4RetryPrefix e cache bytes ds exactRx gen fallback srcIf rt

def send4AfterCachePrefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) : MixedM Int := do
  if ← liftPrefix (branch .send4CacheMiss route.isNone) then
    send4MissPrefix e cache bytes ds exactRx gen route saddr srcIf
  else send4FinishPrefix e bytes ds exactRx route

def send4Prefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) : MixedM Int := do
  let d ← liftPrefix getDev
  if ← liftPrefix (branch .send4SockNull d.sock4.isNone) then return -ENONET
  let gen := (← liftPrefix (get : M World)).ipv4Gen
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← liftPrefix (branch .send4HasCache cache.isSome) then
    let some pid := cache | liftPrefix (invariant "unreachable")
    if let some s ← dstCacheGetPrefix pid gen then
      route := some {dev := s.dev, src := s.src}; saddr := s.src
  send4AfterCachePrefix e cache bytes ds exactRx gen saddr e.srcIf route

theorem send4ClearSrcPrefix_erases (cache : Option PeerId) :
    ErasesPrefix (send4ClearSrcPrefix cache) (send4ClearSrcSource cache) := by
  unfold send4ClearSrcPrefix send4ClearSrcSource
  repeat' first
    | with_reducible exact modifyPeerKeysPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | split
    | (intro x; try dsimp only)

theorem send4FinishPrefix_erases (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) :
    ErasesPrefix (send4FinishPrefix e bytes ds exactRx route) (send4FinishSource e bytes ds exactRx route) := by
  unfold send4FinishPrefix send4FinishSource
  repeat' first
    | with_reducible exact tunnelXmitPrefix_erases _ _ _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | split
    | (intro x; try dsimp only)

theorem send4RouteDonePrefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) :
    ErasesPrefix (send4RouteDonePrefix e cache bytes ds exactRx gen fallback rt) (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  unfold send4RouteDonePrefix send4RouteDoneSource
  repeat' first
    | with_reducible exact send4FinishPrefix_erases _ _ _ _ _
    | with_reducible exact dstCacheSetPrefix_erases _ _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | split
    | (intro x; try dsimp only)

theorem send4RetryPrefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) :
    ErasesPrefix (send4RetryPrefix e cache bytes ds exactRx gen fallback srcIf rt) (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  unfold send4RetryPrefix send4RetrySource
  repeat' first
    | with_reducible exact send4RouteDonePrefix_erases _ _ _ _ _ _ _ _
    | with_reducible exact send4ClearSrcPrefix_erases _
    | with_reducible exact dstCacheResetMixed_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | split
    | (intro x; try dsimp only)

theorem send4MissPrefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) :
    ErasesPrefix (send4MissPrefix e cache bytes ds exactRx gen fallback saddr srcIf) (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  unfold send4MissPrefix send4MissSource
  repeat' first
    | with_reducible exact send4RetryPrefix_erases _ _ _ _ _ _ _ _ _
    | with_reducible exact send4ClearSrcPrefix_erases _
    | with_reducible exact dstCacheResetMixed_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | split
    | (intro x; try dsimp only)

theorem send4AfterCachePrefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) :
    ErasesPrefix (send4AfterCachePrefix e cache bytes ds exactRx gen saddr srcIf route) (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  unfold send4AfterCachePrefix send4AfterCacheSource
  repeat' first
    | with_reducible exact send4MissPrefix_erases _ _ _ _ _ _ _ _ _
    | with_reducible exact send4FinishPrefix_erases _ _ _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | split
    | (intro x; try dsimp only)

theorem send4Prefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    ErasesPrefix (send4Prefix e cache bytes ds exactRx) (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  unfold send4Prefix send4Source
  repeat' first
    | with_reducible exact send4AfterCachePrefix_erases _ _ _ _ _ _ _ _ _
    | with_reducible exact dstCacheGetPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | split
    | (intro x; try dsimp only)

theorem send4ClearSrcPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (cache : Option PeerId) :
    AmbientSpec I P (send4ClearSrcPrefix cache) (fun _ => P) := by
  unfold send4ClearSrcPrefix
  repeat' first
    | with_reducible exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl)
    | with_reducible exact c.kernel P _ getDev_sameKernel
    | with_reducible exact c.kernel P _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact c.kernel P (get : M World) (by intro w x v hr; cases hr; rfl)
    | with_reducible exact c.branch P _ _
    | with_reducible exact c.invariant P _
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.ite
    | with_reducible apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem send4FinishPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) :
    AmbientSpec I P (send4FinishPrefix e bytes ds exactRx route) (fun _ => P) := by
  unfold send4FinishPrefix
  repeat' first
    | with_reducible exact tunnelXmitPrefix_spec c sc P _ _ _ _ _
    | with_reducible exact c.kernel P _ getDev_sameKernel
    | with_reducible exact c.kernel P _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact c.kernel P (get : M World) (by intro w x v hr; cases hr; rfl)
    | with_reducible exact c.branch P _ _
    | with_reducible exact c.invariant P _
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.ite
    | with_reducible apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem send4RouteDonePrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) :
    AmbientSpec I P (send4RouteDonePrefix e cache bytes ds exactRx gen fallback rt) (fun _ => P) := by
  unfold send4RouteDonePrefix
  repeat' first
    | with_reducible exact send4FinishPrefix_spec c sc P _ _ _ _ _
    | with_reducible exact dstCacheSetPrefix_spec c P _ _ _ _
    | with_reducible exact c.kernel P _ getDev_sameKernel
    | with_reducible exact c.kernel P _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact c.kernel P (get : M World) (by intro w x v hr; cases hr; rfl)
    | with_reducible exact c.branch P _ _
    | with_reducible exact c.invariant P _
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.ite
    | with_reducible apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem send4RetryPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) :
    AmbientSpec I P (send4RetryPrefix e cache bytes ds exactRx gen fallback srcIf rt) (fun _ => P) := by
  unfold send4RetryPrefix
  repeat' first
    | with_reducible exact send4RouteDonePrefix_spec c sc P _ _ _ _ _ _ _ _
    | with_reducible exact send4ClearSrcPrefix_spec c P _
    | with_reducible exact dstCacheResetMixed_spec c P _
    | with_reducible exact c.kernel P _ getDev_sameKernel
    | with_reducible exact c.kernel P _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact c.kernel P (get : M World) (by intro w x v hr; cases hr; rfl)
    | with_reducible exact c.branch P _ _
    | with_reducible exact c.invariant P _
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.ite
    | with_reducible apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem send4MissPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) :
    AmbientSpec I P (send4MissPrefix e cache bytes ds exactRx gen fallback saddr srcIf) (fun _ => P) := by
  have getWorld : AmbientSpec I P (liftPrefix (get : M World)) (fun _ => P) :=
    c.kernel P _ (by intro w x v hr; cases hr; rfl)
  unfold send4MissPrefix
  repeat' first
    | exact getWorld
    | with_reducible exact send4RetryPrefix_spec c sc P _ _ _ _ _ _ _ _ _
    | with_reducible exact send4ClearSrcPrefix_spec c P _
    | with_reducible exact dstCacheResetMixed_spec c P _
    | with_reducible exact c.kernel P _ getDev_sameKernel
    | with_reducible exact c.kernel P _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact c.kernel P (get : M World) (by intro w x v hr; cases hr; rfl)
    | with_reducible exact c.branch P _ _
    | with_reducible exact c.invariant P _
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.ite
    | with_reducible apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem send4AfterCachePrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) :
    AmbientSpec I P (send4AfterCachePrefix e cache bytes ds exactRx gen saddr srcIf route) (fun _ => P) := by
  unfold send4AfterCachePrefix
  repeat' first
    | with_reducible exact send4MissPrefix_spec c sc P _ _ _ _ _ _ _ _ _
    | with_reducible exact send4FinishPrefix_spec c sc P _ _ _ _ _
    | with_reducible exact c.kernel P _ getDev_sameKernel
    | with_reducible exact c.kernel P _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact c.kernel P (get : M World) (by intro w x v hr; cases hr; rfl)
    | with_reducible exact c.branch P _ _
    | with_reducible exact c.invariant P _
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.ite
    | with_reducible apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem send4Prefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    AmbientSpec I P (send4Prefix e cache bytes ds exactRx) (fun _ => P) := by
  have getWorld : AmbientSpec I P (liftPrefix (get : M World)) (fun _ => P) :=
    c.kernel P _ (by intro w x v hr; cases hr; rfl)
  unfold send4Prefix
  repeat' first
    | exact getWorld
    | with_reducible exact send4AfterCachePrefix_spec c sc P _ _ _ _ _ _ _ _ _
    | with_reducible exact dstCacheGetPrefix_spec c P _ _
    | with_reducible exact c.kernel P _ getDev_sameKernel
    | with_reducible exact c.kernel P _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact c.kernel P (get : M World) (by intro w x v hr; cases hr; rfl)
    | with_reducible exact c.branch P _ _
    | with_reducible exact c.invariant P _
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.ite
    | with_reducible apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

/-- The clear-source/reset segment used by either IPv4 miss arm retains the
endpoint read and write when the following reset-clock record fails. Premises
name original getter, setter and clock executions, not observer histories. -/
theorem send4_clear_reset_clock_failure (pid : PeerId) (w v : World) (p : Peer)
    (h : List LifetimeEvent) (err : Stop)
    (hd : w.k.wg.isSome = true)
    (hp : (getPeer pid).run w = .ok (p, w))
    (hw : (setPeer pid {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}}).run w = .ok ((), v))
    (ha : v.armRecords = true) (hc : v.dstCacheRecords = true)
    (hf : (hiddenJiffies .dstCacheResetTs).run v = .error err) :
    runPrefix (do send4ClearSrcPrefix (some pid); dstCacheResetMixed pid) w h =
      (.error err, h ++ [.peer (.read pid p.internalId), .peer (.write pid p.internalId)]) := by
  simp [send4ClearSrcPrefix, modifyPeerKeysPrefix, dstCacheResetMixed,
    runPrefix_bind, getPeerMixed_run, setPeerMixed_run, hd, hp, hw, ha, hc, hf,
    List.append_assoc]

end Leanux.Proofs.WG.Lifetimes
