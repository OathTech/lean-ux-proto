import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedFixture
import Leanux.Proofs.WG.Lifetimes.TxCallSource

/-! Fixed source prefixes of the sender's routed transmit call. The original
FD repayment, fixture exit and return conversion remain in the continuation;
none runs when a preceding native call stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Xmit
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Configuration TransmitSecurity CausalJournal

inductive Prepared where
  | routeRefused (error : Int)
  | packetsRefused (error : Int)
  | ready (packets : List Packet) (mtu : Nat)

/-- Literal native guards through the multicast/neighbour cut, before any
fixture root or WireGuard transmit callback. -/
def prepare (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixM Event Prepared := do
  let r ← match ← liftPrefix (Net.routeLookup family 0 addr) with
    | .error err => return .routeRefused err
    | .ok r => pure r
  if r.dev != WG0_IFINDEX then
    liftPrefix (unsupported "a transmit to a local address (not into wg0)")
  if let some d := (← liftPrefix getWG).dev then
    if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
      liftPrefix (unsupported "a transmit after an MTU change took the family's routes into wg0 down")
  liftPrefix Env.fixtureSend
  let opts := { opts with routeMtu := opts.routeMtu <|> (if r.mtu != 0 then some r.mtu else none) }
  match ← liftPrefix (Env.xmitPackets family addr payload opts) with
  | .error e => return .packetsRefused e
  | .ok (packets, mtu) =>
    Driver.multicastObserved family addr
    if family == 4 then liftPrefix (Net.neighbourClassify WG0_IFINDEX)
    pure (.ready packets mtu)

def entered (family addr : Nat) (packets : List Packet) (mtu : Nat) : PrefixM Event Nat :=
  liftWGObserver (hooks.fixtureEnter (.transmit family addr packets mtu))

def bodyTail (family addr : Nat) (payload : List UInt8) : Prepared → PrefixM Event Int
  | .routeRefused err | .packetsRefused err => pure err
  | .ready packets mtu => do
    let ret ← liftWGObserver (FixtureEffects.runWith (Driver.fixtureOps hooks)
      (.transmit family addr packets mtu) (Driver.transmitObserved hooks family addr packets mtu))
    pure (if ret == 0 then payload.length else ret)

private theorem bind_same {m : Type → Type} [Monad m] (head : m α) {left right : α → m β}
    (same : ∀ value, left value=right value) : (head >>= left)=(head >>= right) :=
  congrArg (fun tail=>head >>= tail) (funext same)

theorem body_factor (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    syscallXmitWith Driver.multicastObserved
      (fun family addr packets mtu => liftWGObserver
        (FixtureEffects.runWith (Driver.fixtureOps hooks) (.transmit family addr packets mtu)
          (Driver.transmitObserved hooks family addr packets mtu))) family addr payload opts =
    socketCallOnWith (fun {_} a => liftPrefix a) SENDER_FD
      (prepare family addr payload opts >>= bodyTail family addr payload) := by
  unfold syscallXmitWith prepare
  congr 1
  repeat' first
    | rfl
    | simp only [bind_assoc,pure_bind,bodyTail]
    | split
    | apply bind_same
    | intro
  all_goals simp_all

inductive Decision where
  | badFd
  | refused (fd : Fd) (error : Int)
  | transmit (fd : Fd) (packets : List Packet) (mtu token : Nat)

/-- Fixed source prefix from SENDER_FD acquisition to fixture entry. -/
def callPrefix (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) : PrefixM Event Decision := do
  let fd ← liftPrefix (liftFS (fdget SENDER_FD))
  if fd.file.isNone then return .badFd
  match ← prepare family addr payload opts with
  | .routeRefused err | .packetsRefused err => pure (.refused fd err)
  | .ready packets mtu => do
    let token ← entered family addr packets mtu
    pure (.transmit fd packets mtu token)

def callTail (family addr : Nat) (payload : List UInt8) : Decision → PrefixM Event Int
  | .badFd => pure (-EBADF)
  | .refused fd err => do
    liftPrefix (liftFS (fdput fd))
    pure err
  | .transmit fd packets mtu token => do
    let ret ← liftWGObserver (Driver.transmitObserved hooks family addr packets mtu)
    liftWGObserver (hooks.fixtureLeave token)
    liftPrefix (liftFS (fdput fd))
    pure (if ret == 0 then payload.length else ret)

theorem whole_factor (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Driver.syscallXmitObserved hooks family addr payload opts =
      (callPrefix family addr payload opts >>= callTail family addr payload) := by
  change syscallXmitWith _ _ _ _ _ _ = _
  rw [body_factor]
  unfold socketCallOnWith callPrefix
  simp only [bind_assoc]
  congr 1
  funext fd
  split
  · simp only [pure_bind,callTail]
  · simp only [bind_assoc]
    congr 1
    funext prepared
    cases prepared with
    | routeRefused err => simp only [bodyTail,pure_bind,callTail]
    | packetsRefused err => simp only [bodyTail,pure_bind,callTail]
    | ready packets mtu =>
      simp only [bodyTail,FixtureEffects.runWith,liftWGObserver_bind,bind_assoc,pure_bind,
        entered,Driver.fixtureOps,callTail]
      rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Xmit
