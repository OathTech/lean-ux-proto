import Leanux.Proofs.WG.Packets.TxFront
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalSource

/-! The actual transmit front with its staged trim and reference repayments
exposed as callbacks. It retains every native error arm and the final splice;
no conservation or initialized reachability premise is built into the source. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Packets

structure Ops (m : Type → Type) where
  step : {α : Type} → WG.M α → m α
  put : Option PeerId → m Unit
  trim : PeerId → m Unit
  splice : PeerId → List Packet → m Unit

def native : Ops WG.M where
  step := id
  put := peerPut
  trim := xmitTrim
  splice := xmitSplice

def selectWith [Monad m] (o : Ops m) (family : Nat) (pkts : List Packet)
    (mtu : Nat) (peer : Option PeerId) : m (Except Int (PeerId × List Packet)) := do
  if ← o.step (branch .xmitNoPeer peer.isNone) then
    if !(← o.step (branch .xmitNoPeerInet (family == 4))) then
      _ ← o.step (branch .xmitNoPeerInet6 (family == 6))
    return .error (← o.step (txError family (pkts.head?.getD {bytes := []}) (-ENOKEY)))
  let some pid := peer | o.step (invariant "unreachable")
  let epFamily := (← o.step (getPeer pid)).endpoint.map (·.family) |>.getD 0
  if ← o.step (WG.andM (branch .xmitEndpointNotInet (epFamily != AF_INET))
      (branch .xmitEndpointNotInet6 (epFamily != AF_INET6))) then
    o.put peer
    return .error (← o.step (txError family (pkts.head?.getD {bytes := []}) (-EDESTADDRREQ)))
  _ ← o.step (branch .xmitValidDst true)
  if !(← o.step (branch .xmitNotGso (pkts.length < 2))) then
    if ← o.step (branch .xmitGsoError !(← o.step (envOk .skbSegment))) then
      o.put peer
      return .error (← o.step (txError family (pkts.head?.getD {bytes := []}) (-ENOMEM)))
  let packets ← o.step (txWalk pkts mtu [])
  _ ← o.step (branch .xmitWalk false)
  o.trim pid
  return .ok (pid,packets)

def frontWith [Monad m] (o : Ops m) (family addr : Nat) (pkts : List Packet)
    (mtu : Nat) : m (Except Int PeerId) := do
  if !(← o.step (txCheck family addr pkts mtu)) then return .error (-EPROTONOSUPPORT)
  let peer ← o.step (lookupDst family addr)
  match ← selectWith o family pkts mtu peer with
  | .error err => pure (.error err)
  | .ok (pid,packets) =>
    o.splice pid packets
    pure (.ok pid)

theorem select_native (family : Nat) (pkts : List Packet) (mtu : Nat) (peer : Option PeerId) :
    selectWith native family pkts mtu peer = txSelect family pkts mtu peer := rfl

theorem front_native (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    frontWith native family addr pkts mtu = txFront family addr pkts mtu := rfl

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
