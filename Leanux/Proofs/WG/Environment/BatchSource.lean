import Leanux.Env

/-! Source-only batch item cut. The complete original equation below is checked
without state, input or success premises. -/
namespace Leanux.Proofs.WG.Environment
open Leanux Leanux.WG Leanux.Env

def batchItemSource (d : Device) (cqes : List Int) (item : BatchItem) : M (ForInStep (List Int)) := do
  let mut cqes := cqes
  match item with
  | .inject family port msg =>
    if port != d.incomingPort then unsupported "a batch datagram to a port other than wg0's"
    fixtureSend
    let src ← senderSource family 0
    runWorker .netRx do
      WG.wgReceive msg src
      pollScheduledInline
    cqes := cqes ++ [(msg.length : Int)]
  | .xmit family addr payload opts =>
    -- W9: the sender's `sendto` routes on the fixture's tables; a local
    -- destination never reaches wg0
    match ← routeLookup family 0 addr with
    | .error err => cqes := cqes ++ [err]
    | .ok r =>
      if r.dev != WG0_IFINDEX then unsupported "a batch transmit to a local address (not into wg0)"
      if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
        unsupported "a transmit after an MTU change took the family's routes into wg0 down"
      fixtureSend
      match ← xmitPackets family addr payload opts with
      | .error e => cqes := cqes ++ [e]
      | .ok (pkts, mtu) =>
        xmitMulticastLoop family addr
        let ret ← WG.wgXmit family addr pkts mtu
        cqes := cqes ++ [if ret == 0 then (payload.length : Int) else ret]
  return .yield cqes

def batchSource (items : List BatchItem) : M Int := do
  let some d := (← getK).wg | unsupported "a batch without wg0"
  if !d.running then unsupported "a batch with wg0 down"
  for pid in d.peerList do requireNotPending pid "a batch while a handshake is queued"
  let cqes ← forIn items ([] : List Int) (fun item cqes => batchItemSource d cqes item)
  modify fun w => { w with extraOut := [("cqes", Lean.toJson cqes)] }
  afterBatch
  return items.length

theorem batchSource_eq (items : List BatchItem) : batchSource items = Env.batch items := rfl

end Leanux.Proofs.WG.Environment
