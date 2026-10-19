import Leanux.Proofs.WG.TransmitSecurity.CompletionSource
import Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffectsProjection

/-! TX completion exposes timer and queue effects without replacing its
existing lifetime accesses, packet-read receipts, or actual socket receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

structure Ops (E : Type) where
  step : {α : Type} → WG.M α → PrefixM E α
  peer : PeerId → PrefixM E Peer
  modifyPeer : PeerId → (Peer → Peer) → PrefixM E Unit
  packet : SkbId → PrefixM E DataPacket
  completion : PeerId → List SkbId → PrefixM E Unit
  send : PeerId → SkbId → RunWitness DataPacket → PrefixM E Bool
  drop : PeerId → List SkbId → PrefixM E Unit
  dispose : PeerId → List SkbId → KeypairId → PrefixM E Bool
  traversal : PeerId → PrefixM E Unit
  sent : PeerId → PrefixM E Unit
  dataSent : PeerId → PrefixM E Unit
  fresh : PeerId → PrefixM E Unit

def native : Ops Completion.Event where
  step := fun a => liftPrefix (liftWG a)
  peer := fun pid => Completion.access (getPeerMixed pid)
  modifyPeer := fun pid f => Completion.access (modifyPeerKeysPrefix pid f)
  packet := fun id => Completion.access (getTxSkbPrefix id)
  completion := fun pid item => emitPrefix (.disposition (.completion pid item))
  send := Completion.send
  drop := fun pid item => focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.drop pid item)
  dispose := fun pid item key => focusPrefix Completion.Event.disposition Completion.disposition? (TxDisposition.dispose pid item key)
  traversal := fun pid => Completion.access (timersTraversalPrefix pid)
  sent := fun pid => Completion.access (timersAnyAuthenticatedPacketSentPrefix pid)
  dataSent := fun pid => Completion.access (timersDataSentPrefix pid)
  fresh := fun pid => Completion.access (keepKeyFreshPrefix pid)

def completeWith (o : Ops E) (pid : PeerId) (item : List SkbId) : PrefixM E Unit := do
  o.completion pid item
  o.traversal pid
  o.sent pid
  let mut dataSent := false
  for id in item do
    let packet ← captureObserved (o.packet id)
    _ ← o.step (branch .doneSkbIterate true)
    let isKeepalive := packet.value.bytes.length == MESSAGE_DATA_LEN_0
    let sent ← o.send pid id packet
    if ← TxDisposition.andObs (o.step (branch .doneSendOk sent))
        (o.step (branch .doneNotKeepalive !isKeepalive)) then dataSent := true
  _ ← o.step (branch .doneSkbIterate false)
  if ← o.step (branch .doneDataSent dataSent) then o.dataSent pid
  o.fresh pid

def bodyWith (o : Ops E) (pid : PeerId) (first : Option (List SkbId)) : PrefixM E Bool := do
  let go ← TxDisposition.andObs (o.step (branch .txPacket first.isSome)) do
    let some f := first | o.step (invariant "unreachable")
    let some h := f.head? | o.step (invariant "an empty ring item")
    o.step (branch .txNotUncrypted ((← o.packet h).state != .uncrypted))
  if !go then return false
  let some item := first | o.step (invariant "unreachable")
  let some headId := item.head? | o.step (invariant "an empty ring item")
  let head ← o.packet headId
  o.drop pid item
  if ← o.step (branch .txCrypted (head.state == .crypted)) then completeWith o pid item
  o.dispose pid item head.keypair

def stepWith (o : Ops E) (pid : PeerId) : PrefixM E Bool := do
  let (first,q) ← o.step ((← o.peer pid).txQueue.peek)
  o.modifyPeer pid fun p => {p with txQueue := q}
  bodyWith o pid first

theorem complete_factor (pid : PeerId) (item : List SkbId) :
    completeWith native pid item = Completion.complete pid item := rfl
theorem body_factor (pid : PeerId) (first : Option (List SkbId)) :
    bodyWith native pid first = Completion.body pid first := rfl
theorem step_factor (pid : PeerId) : stepWith native pid = Completion.step pid := rfl

end Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
