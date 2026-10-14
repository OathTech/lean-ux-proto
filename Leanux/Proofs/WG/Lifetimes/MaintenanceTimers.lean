import Leanux.Proofs.WG.Lifetimes.ReceiveEntry

set_option maxHeartbeats 600000
set_option pp.structureInstances false

/-! Endpoint and receive-timer maintenance with explicit resolved-peer
accesses. The generic contracts use the existing immediate read/update helper.
Time records retain their original validation; these are lifetime contracts. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem endpointEq_sameKernel (a : Endpoint) (b : Option Endpoint) :
    SameKernel (endpointEq a b) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [endpointEq, WG.andM, branch]

def dstCacheResetMixed (pid : PeerId) : MixedM Unit := do
  let w ← liftPrefix (get : M World)
  if !(w.armRecords && w.dstCacheRecords) then return
  let ts ← liftPrefix (hiddenJiffies .dstCacheResetTs)
  modifyPeerKeysPrefix pid fun p => {p with dstCache := {p.dstCache with resetTs := ts}}

theorem dstCacheResetMixed_erases (pid : PeerId) :
    ErasesPrefix (dstCacheResetMixed pid) (dstCacheReset pid) := by
  unfold dstCacheResetMixed dstCacheReset
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro w
  split
  · exact erasesPrefix_pure _
  · exact erasesPrefix_bind (erasesPrefix_lift _)
      (fun _ => modifyPeerKeysPrefix_erases _ _)

theorem dstCacheResetMixed_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (dstCacheResetMixed pid) (fun _ => P) := by
  unfold dstCacheResetMixed
  apply PrefixEnsures.bind (c.kernel P get (by intro w x v hr; cases hr; rfl))
  intro w
  split
  · exact c.pure P _
  · apply PrefixEnsures.bind (c.kernel P _ (hiddenJiffies_sameKernel _))
    intro ts
    exact modifyPeerKeysPrefix_spec_ambient c P pid _ (fun _ => rfl)

def setPeerEndpointPrefix (pid : PeerId) (e : Endpoint) : MixedM Unit := do
  requireNotPendingMixed pid "changing the endpoint"
  if ← liftPrefix (branch .setEndpointEq (← liftPrefix (endpointEq e (← getPeerMixed pid).endpoint))) then return
  if ← liftPrefix (branch .setEndpointV4 (e.family == AF_INET)) then
    modifyPeerKeysPrefix pid fun p => {p with endpoint := some e}
    dstCacheResetMixed pid
  else if ← liftPrefix (branch .setEndpointV6 (e.family == AF_INET6)) then
    modifyPeerKeysPrefix pid fun p => {p with endpoint := some e}
    dstCacheResetMixed pid

theorem setPeerEndpointPrefix_erases (pid : PeerId) (e : Endpoint) :
    ErasesPrefix (setPeerEndpointPrefix pid e) (setPeerEndpoint pid e) := by
  have update : ErasesPrefix
      (do modifyPeerKeysPrefix pid (fun p => {p with endpoint := some e}); dstCacheResetMixed pid)
      (do setPeer pid {(← getPeer pid) with endpoint := some e}; dstCacheReset pid) := by
    simp only [modifyPeerKeysPrefix, bind_assoc]
    exact erasesPrefix_bind (getPeerMixed_erases _) (fun _ =>
      erasesPrefix_bind (setPeerMixed_erases _ _) (fun _ => dstCacheResetMixed_erases _))
  unfold setPeerEndpointPrefix setPeerEndpoint
  apply erasesPrefix_bind (requireNotPendingMixed_erases _ _)
  intro _
  apply erasesPrefix_bind (getPeerMixed_erases _)
  intro p
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro equal
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro yes
  split
  · exact erasesPrefix_pure _
  · apply erasesPrefix_bind (erasesPrefix_lift _)
    intro v4
    split
    · exact update
    · apply erasesPrefix_bind (erasesPrefix_lift _)
      intro v6
      split
      · exact update
      · exact erasesPrefix_pure _

theorem setPeerEndpointPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (e : Endpoint) : AmbientSpec I P (setPeerEndpointPrefix pid e) (fun _ => P) := by
  unfold setPeerEndpointPrefix
  repeat' first
    | exact requireNotPendingMixed_spec c P _ _
    | exact c.getPeer_frame P _
    | exact c.kernel P _ (endpointEq_sameKernel _ _)
    | exact c.branch P _ _
    | exact c.branchCmp P _ _ _ _
    | exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl)
    | exact dstCacheResetMixed_spec c P _
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

/-- The access-free prelude of the original timer arm. Its world updates and
hidden-input failures occur before the first resolved peer read. -/
def timerArmExpiry (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) : M UInt64 := do
  let w ← get
  let e ← if w.armRecords then
      let bs ← hidden .modTimerArm
      let (jm, e) := (recordWord64 bs 0, recordWord64 bs 1)
      let some caller := jc | invariant "a timer armed with arm records and no caller read (kind 311)"
      let expires := caller + delay.toUInt64
      if expires != e then
        throw (.hidden s!"timer expiry differs from Linux: the caller read jiffies {caller} and mod_timer published {e}; the mirror's delay {delay} gives {expires}")
      let gap := (jm - caller).toInt64
      if gap < 0 then
        throw (.hidden s!"mod_timer's jiffies {jm} is behind the caller's read {caller} (delay {delay}, expires {e})")
      if gap > 1 then
        unsupported s!"a stall between a timer's two jiffies reads: the caller's {caller}, mod_timer's {jm} (delay {delay}, expires {e})"
      modify fun w => {w with jiffiesLast := some jm}
      let u := recordWord bs 2
      if u != 0 then modify fun w => {w with timerUnits := (u, pid, t) :: w.timerUnits.filter (·.1 != u)}
      return e
    else return w.jiffiesLast.getD 0 + delay.toUInt64
  pure e

theorem timerArmExpiry_sameKernel (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameKernel (timerArmExpiry pid t delay jc) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (hidden_sameKernel .modTimerArm) (fun k' => k' = k)
  mvcgen [timerArmExpiry, hs, unsupported, invariant]

theorem armTimer_source (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    armTimer pid t delay jc = (do
      let e ← timerArmExpiry pid t delay jc
      setPeer pid ((← getPeer pid).setTimer t (some e))) := by
  have ib {α β : Type} (c : Prop) [Decidable c] (a b : M α) (f : α → M β) :
      ((if c then a else b) >>= f) = (if c then a >>= f else b >>= f) := by
    split <;> rfl
  cases jc <;> simp only [armTimer, timerArmExpiry, bind_assoc, pure_bind, ib]
  all_goals rfl

def armTimerPrefix (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) : MixedM Unit := do
  let e ← liftPrefix (timerArmExpiry pid t delay jc)
  modifyPeerKeysPrefix pid fun p => p.setTimer t (some e)

def delTimerPrefix (pid : PeerId) (t : PeerTimer) : MixedM Unit :=
  modifyPeerKeysPrefix pid fun p => p.setTimer t none

theorem armTimerPrefix_erases (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    ErasesPrefix (armTimerPrefix pid t delay jc) (armTimer pid t delay jc) := by
  rw [armTimer_source pid t delay jc]
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => modifyPeerKeysPrefix_erases _ _)

theorem delTimerPrefix_erases (pid : PeerId) (t : PeerTimer) :
    ErasesPrefix (delTimerPrefix pid t) (delTimer pid t) := modifyPeerKeysPrefix_erases _ _

theorem armTimerPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) : AmbientSpec I P (armTimerPrefix pid t delay jc) (fun _ => P) := by
  apply PrefixEnsures.bind (c.kernel P _ (timerArmExpiry_sameKernel pid t delay jc))
  intro e
  exact modifyPeerKeysPrefix_spec_ambient c P pid _ (fun p => by cases t <;> rfl)

theorem delTimerPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (t : PeerTimer) : AmbientSpec I P (delTimerPrefix pid t) (fun _ => P) :=
  modifyPeerKeysPrefix_spec_ambient c P pid _ (fun p => by cases t <;> rfl)

/-- The original nested arrow resolves the peer before evaluating andM.
Keeping that elaborated order is necessary even when running is false. -/
def modPeerTimerGuardPrefix (pid : PeerId) : MixedM Bool := do
  let running := (← liftPrefix getDev).running
  let alive := !(← getPeerMixed pid).isDead
  liftPrefix (WG.andM (branch .modTimerRunning running) (branch .modTimerAlive alive))

theorem modPeerTimerGuardPrefix_erases (pid : PeerId) :
    ErasesPrefix (modPeerTimerGuardPrefix pid) (modPeerTimerGuard pid) := by
  unfold modPeerTimerGuardPrefix modPeerTimerGuard
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
    erasesPrefix_bind (getPeerMixed_erases _) (fun _ => erasesPrefix_lift _))

theorem modPeerTimerGuardPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (modPeerTimerGuardPrefix pid) (fun _ => P) := by
  apply PrefixEnsures.bind (c.kernel P _ getDev_sameKernel)
  intro d
  apply PrefixEnsures.bind (c.getPeer_frame P pid)
  intro p
  apply c.kernel P
  unfold WG.andM
  exact sameKernel_bind (sameKernel_branch _ _) (fun b => by
    split
    · exact sameKernel_branch _ _
    · exact sameKernel_pure _)

def modPeerTimerPrefix (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) : MixedM Bool := do
  let jc ← liftPrefix (callerJiffies site)
  if ← modPeerTimerGuardPrefix pid then
    armTimerPrefix pid t delay jc
    return true
  return false

theorem modPeerTimerPrefix_erases (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    ErasesPrefix (modPeerTimerPrefix site pid t delay) (modPeerTimer site pid t delay) := by
  unfold modPeerTimerPrefix modPeerTimer
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro jc
  apply erasesPrefix_bind (modPeerTimerGuardPrefix_erases pid)
  intro b
  split
  · exact erasesPrefix_bind (armTimerPrefix_erases pid t delay jc) (fun _ => erasesPrefix_pure _)
  · exact erasesPrefix_pure _

theorem modPeerTimerPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    AmbientSpec I P (modPeerTimerPrefix site pid t delay) (fun _ => P) := by
  unfold modPeerTimerPrefix
  apply PrefixEnsures.bind (c.kernel P _ (callerJiffies_sameKernel site))
  intro jc
  apply PrefixEnsures.bind (modPeerTimerGuardPrefix_spec c P pid)
  intro b
  split
  · exact PrefixEnsures.bind (armTimerPrefix_spec c P pid t delay jc) (fun _ => c.pure P _)
  · exact c.pure P _

def timersHandshakeCompletePrefix (pid : PeerId) (site : HiddenSite := .walltimeLastHandshake) : MixedM Unit := do
  delTimerPrefix pid .retransmitHandshake
  modifyPeerKeysPrefix pid fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}
  let now ← liftPrefix (hidden site)
  modifyPeerKeysPrefix pid fun p => {p with walltimeLastHandshake := now}

def timersAnyAuthenticatedPacketReceivedPrefix (pid : PeerId) : MixedM Unit :=
  delTimerPrefix pid .newHandshake

def timersDataReceivedPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftPrefix (branch .timersDataReceivedRunning (← liftPrefix getDev).running) then
    if ← liftPrefix (branch .timersDataReceivedNotPending !((← getPeerMixed pid).timerPending .sendKeepalive)) then
      discard <| modPeerTimerPrefix .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS
    else
      modifyPeerKeysPrefix pid fun p => {p with timerNeedAnotherKeepalive := true}

def timersTraversalPrefix (pid : PeerId) : MixedM Unit := do
  let interval := (← getPeerMixed pid).persistentKeepaliveInterval
  if ← liftPrefix (branchCmp .traversalKeepalive (interval != 0) interval 0) then
    discard <| modPeerTimerPrefix .timerJiffiesTraversal pid .persistentKeepalive (interval * HZ)

theorem timersHandshakeCompletePrefix_erases (pid : PeerId) (site : HiddenSite) :
    ErasesPrefix (timersHandshakeCompletePrefix pid site) (timersHandshakeComplete pid site) := by
  unfold timersHandshakeCompletePrefix timersHandshakeComplete
  simp only [modifyPeerKeysPrefix, bind_assoc]
  exact erasesPrefix_bind (delTimerPrefix_erases _ _) (fun _ =>
    erasesPrefix_bind (getPeerMixed_erases _) (fun _ =>
      erasesPrefix_bind (setPeerMixed_erases _ _) (fun _ =>
        erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
          erasesPrefix_bind (getPeerMixed_erases _) (fun _ => setPeerMixed_erases _ _)))))

theorem timersAnyAuthenticatedPacketReceivedPrefix_erases (pid : PeerId) :
    ErasesPrefix (timersAnyAuthenticatedPacketReceivedPrefix pid) (timersAnyAuthenticatedPacketReceived pid) :=
  delTimerPrefix_erases _ _

theorem timersDataReceivedPrefix_erases (pid : PeerId) :
    ErasesPrefix (timersDataReceivedPrefix pid) (timersDataReceived pid) := by
  unfold timersDataReceivedPrefix timersDataReceived
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | exact getPeerMixed_erases _
    | exact setPeerMixed_erases _ _
    | exact modPeerTimerPrefix_erases _ _ _ _
    | exact modifyPeerKeysPrefix_erases _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | split
    | (intro x; try dsimp only)
    | rfl

theorem timersTraversalPrefix_erases (pid : PeerId) :
    ErasesPrefix (timersTraversalPrefix pid) (timersTraversal pid) := by
  unfold timersTraversalPrefix timersTraversal
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | exact getPeerMixed_erases _
    | exact setPeerMixed_erases _ _
    | exact modPeerTimerPrefix_erases _ _ _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | split
    | (intro x; try dsimp only)
    | rfl

theorem timersHandshakeCompletePrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (site : HiddenSite) : AmbientSpec I P (timersHandshakeCompletePrefix pid site) (fun _ => P) := by
  unfold timersHandshakeCompletePrefix
  apply PrefixEnsures.bind (delTimerPrefix_spec c P _ _)
  intro _
  apply PrefixEnsures.bind (modifyPeerKeysPrefix_spec_ambient c P pid
    (fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}) (fun _ => rfl))
  intro _
  apply PrefixEnsures.bind (c.kernel P _ (hidden_sameKernel site))
  intro now
  exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl)

theorem timersAnyAuthenticatedPacketReceivedPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : AmbientSpec I P (timersAnyAuthenticatedPacketReceivedPrefix pid) (fun _ => P) :=
  delTimerPrefix_spec c P _ _

theorem timersDataReceivedPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : AmbientSpec I P (timersDataReceivedPrefix pid) (fun _ => P) := by
  unfold timersDataReceivedPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | exact c.kernel P _ getDev_sameKernel
    | exact c.getPeer_frame P _
    | exact c.branch P _ _
    | exact c.branchCmp P _ _ _ _
    | exact modPeerTimerPrefix_spec c P _ _ _ _
    | exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl)
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem timersTraversalPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : AmbientSpec I P (timersTraversalPrefix pid) (fun _ => P) := by
  unfold timersTraversalPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | exact c.getPeer_frame P _
    | exact c.branch P _ _
    | exact c.branchCmp P _ _ _ _
    | exact modPeerTimerPrefix_spec c P _ _ _ _
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
