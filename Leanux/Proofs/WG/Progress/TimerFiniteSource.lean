import Leanux.Proofs.WG.Progress.KeepaliveFiniteSource
import Leanux.Proofs.WG.TimerDiscipline.HookDeferredSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.TimerFinite
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues

/-- Finite keepalive at the actual expiry callback, before the rearm guard. -/
def keepalive (pid : PeerId) : WG.M Unit := do
  HandshakeFinite.keepalive pid
  if ← branch .keepaliveNeedAnother (← getPeer pid).timerNeedAnotherKeepalive then
    setPeer pid { (← getPeer pid) with timerNeedAnotherKeepalive := false }
    discard <| modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS

theorem keepalive_source (pid : PeerId) :
    WG.expiredSendKeepalive pid = keepalive pid := by
  unfold keepalive
  rw [← HandshakeFinite.keepalive_source]
  rfl

/-- The interval guard still precedes finite persistent keepalive evaluation. -/
def persistent (pid : PeerId) : WG.M Unit := do
  if ← branch .persistentKeepaliveInterval ((← getPeer pid).persistentKeepaliveInterval != 0) then
    HandshakeFinite.keepalive pid

theorem persistent_source (pid : PeerId) :
    WG.expiredSendPersistentKeepalive pid = persistent pid := by
  unfold persistent
  rw [← HandshakeFinite.keepalive_source]
  rfl

/-- All five concrete callbacks; the other three only enqueue or clear work. -/
def callback (pid : PeerId) : PeerTimer → WG.M Unit
  | .retransmitHandshake => WG.expiredRetransmitHandshake pid
  | .sendKeepalive => keepalive pid
  | .newHandshake => WG.expiredNewHandshake pid
  | .zeroKeyMaterial => WG.expiredZeroKeyMaterial pid
  | .persistentKeepalive => persistent pid

theorem callback_source (pid : PeerId) (timer : PeerTimer) :
    WG.timerCallback pid timer = callback pid timer := by
  cases timer <;> simp only [WG.timerCallback, callback, keepalive_source, persistent_source]

/-- Local finite variant of Logged.timerDispatchUnit. Guards, section records,
wheel metadata and the post-callback reset retain their native order. -/
def dispatch (w : Worker) (pid : PeerId) (t : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) : Leanux.M Unit := do
  let expected ← Env.timerWorker t
  if w != expected then
    throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}")
  if let some u ← peekUnit w then
    match (← getWG).timerUnits.find? (·.1 == u) with
    | some (_, pid', t') =>
      if pid' != pid || t' != t then
        throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}")
    | none => throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})")
  if let some b := step then
    if b != we.bucketExpiry then Env.requireStepComplete b
  delTimer pid t
  modifyWG fun s => { s with timerPassStep := some we.bucketExpiry }
  Env.runTimerSection w (callback pid t)
  modifyWG fun s => { s with timerPassStep := none }

theorem dispatch_source (w : Worker) (pid : PeerId) (t : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) :
    timerDispatchUnit w pid t we step = dispatch w pid t we step := by
  unfold dispatch
  rw [← callback_source]
  rfl

/-- The captured placeholder bound and wheel scan, with finite callbacks. -/
def placeholder (jHi : UInt64) : Leanux.M Unit := do
  let pending := (← getDev).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let d ← getDev
    let some (pid, t, _) := TimerWheel.nextDue d jHi | break
    delTimer pid t
    Env.runTimerSection (← Env.timerWorker t) (callback pid t)

theorem placeholder_source (jHi : UInt64) :
    RxHistory.placeholderTimerPassSource jHi = placeholder jHi := by
  unfold RxHistory.placeholderTimerPassSource placeholder
  simp only [callback_source]
  rfl

end Leanux.Proofs.WG.Progress.TimerFinite
