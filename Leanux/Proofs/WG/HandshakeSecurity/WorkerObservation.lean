import Leanux.Proofs.WG.HandshakeSecurity.Increasing
import Leanux.Proofs.WG.Origins.HandshakeSources

/-! Exact timestamp observation through the original handshake worker. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Worker
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Origins.HandshakeSources

def ops : Ops (WGPrefix TimestampReceipt) where
  step := liftWGPrefix
  session := fun pid => liftWGPrefix (beginSession pid)
  modifyPeer := fun pid f => liftWGPrefix (do setPeer pid (f (← getPeer pid)))
  create := fun pid => liftWGPrefix (createResponse pid)
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  derived := fun pid => liftWGPrefix (timersSessionDerived pid)
  traversal := fun pid => liftWGPrefix (timersTraversal pid)
  sent := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketSent pid)
  cookie := fun msg src => liftWGPrefix (sendHandshakeCookie msg src)
  initiation := consumeObserved
  response := fun msg => liftWGPrefix (consumeResponse msg)
  endpoint := fun pid src => liftWGPrefix (setPeerEndpointFromSkb pid src)
  complete := fun pid => liftWGPrefix (timersHandshakeComplete pid)
  keepalive := fun pid => liftWGPrefix (sendKeepalive pid)
  received := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketReceived pid)
  put := fun peer => liftWGPrefix (peerPut peer)
  cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)

def observed : WGPrefix TimestampReceipt Bool := stepWith ops

private theorem lifted {α : Type} (action : WG.M α) :
    ErasesStatePrefix (liftWGPrefix action : WGPrefix TimestampReceipt α) action :=
  erasesStatePrefix_lift action

private theorem erases_step {α : Type} (a : WG.M α) :
    ErasesStatePrefix (ops.step a) (original.step a) :=
  lifted _

private theorem erases_session (pid : PeerId) :
    ErasesStatePrefix (ops.session pid) (original.session pid) :=
  lifted _

private theorem erases_modifyPeer (pid : PeerId) (f : Peer → Peer) :
    ErasesStatePrefix (ops.modifyPeer pid f) (original.modifyPeer pid f) :=
  lifted _

private theorem erases_create (pid : PeerId) :
    ErasesStatePrefix (ops.create pid) (original.create pid) :=
  lifted _

private theorem erases_mac (pid : PeerId) (msg : List UInt8) :
    ErasesStatePrefix (ops.mac pid msg) (original.mac pid msg) :=
  lifted _

private theorem erases_send (pid : PeerId) (msg : List UInt8) :
    ErasesStatePrefix (ops.send pid msg) (original.send pid msg) :=
  lifted _

private theorem erases_derived (pid : PeerId) :
    ErasesStatePrefix (ops.derived pid) (original.derived pid) :=
  lifted _

private theorem erases_traversal (pid : PeerId) :
    ErasesStatePrefix (ops.traversal pid) (original.traversal pid) :=
  lifted _

private theorem erases_sent (pid : PeerId) :
    ErasesStatePrefix (ops.sent pid) (original.sent pid) :=
  lifted _

private theorem erases_cookie (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (ops.cookie msg src) (original.cookie msg src) :=
  lifted _

private theorem erases_initiation (msg : List UInt8) :
    ErasesStatePrefix (ops.initiation msg) (original.initiation msg) :=
  consume_erases msg

private theorem erases_response (msg : List UInt8) :
    ErasesStatePrefix (ops.response msg) (original.response msg) :=
  lifted _

private theorem erases_endpoint (pid : PeerId) (src : SkbSource) :
    ErasesStatePrefix (ops.endpoint pid src) (original.endpoint pid src) :=
  lifted _

private theorem erases_complete (pid : PeerId) :
    ErasesStatePrefix (ops.complete pid) (original.complete pid) :=
  lifted _

private theorem erases_keepalive (pid : PeerId) :
    ErasesStatePrefix (ops.keepalive pid) (original.keepalive pid) :=
  lifted _

private theorem erases_received (pid : PeerId) :
    ErasesStatePrefix (ops.received pid) (original.received pid) :=
  lifted _

private theorem erases_put (peer : Option PeerId) :
    ErasesStatePrefix (ops.put peer) (original.put peer) :=
  lifted _

private theorem erases_cookieConsume (msg : List UInt8) :
    ErasesStatePrefix (ops.cookieConsume msg) (original.cookieConsume msg) :=
  lifted _

private theorem erases_if {α : Type} (c : Prop) [Decidable c]
    (x y : WGPrefix TimestampReceipt α) (a b : WG.M α)
    (hx : ErasesStatePrefix x a) (hy : ErasesStatePrefix y b) :
    ErasesStatePrefix (if c then x else y) (if c then a else b) := by
  split <;> assumption

private theorem response_erases (pid : PeerId) :
    ErasesStatePrefix (responseWith ops pid) (responseWith original pid) := by
  unfold responseWith
  repeat' first
    | with_reducible exact erases_step _
    | with_reducible exact erases_session _
    | with_reducible exact erases_modifyPeer _ _
    | with_reducible exact erases_create _
    | with_reducible exact erases_mac _ _
    | with_reducible exact erases_send _ _
    | with_reducible exact erases_derived _
    | with_reducible exact erases_traversal _
    | with_reducible exact erases_sent _
    | with_reducible exact erases_cookie _ _
    | with_reducible exact erases_initiation _
    | with_reducible exact erases_response _
    | with_reducible exact erases_endpoint _ _
    | with_reducible exact erases_complete _
    | with_reducible exact erases_keepalive _
    | with_reducible exact erases_received _
    | with_reducible exact erases_put _
    | with_reducible exact erases_cookieConsume _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | with_reducible apply erases_if
    | split

private theorem afterMac_erases (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (mac : MacState) :
    ErasesStatePrefix (afterMacWith ops msg src loaded mac)
      (afterMacWith original msg src loaded mac) := by
  unfold afterMacWith
  repeat' first
    | with_reducible exact erases_step _
    | with_reducible exact erases_session _
    | with_reducible exact erases_modifyPeer _ _
    | with_reducible exact erases_create _
    | with_reducible exact erases_mac _ _
    | with_reducible exact erases_send _ _
    | with_reducible exact erases_derived _
    | with_reducible exact erases_traversal _
    | with_reducible exact erases_sent _
    | with_reducible exact erases_cookie _ _
    | with_reducible exact erases_initiation _
    | with_reducible exact erases_response _
    | with_reducible exact erases_endpoint _ _
    | with_reducible exact erases_complete _
    | with_reducible exact erases_keepalive _
    | with_reducible exact erases_received _
    | with_reducible exact erases_put _
    | with_reducible exact erases_cookieConsume _
    | with_reducible exact response_erases _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | with_reducible apply erases_if
    | split

private theorem reception_erases (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (receptionWith ops msg src) (receptionWith original msg src) := by
  unfold receptionWith
  repeat' first
    | with_reducible exact erases_step _
    | with_reducible exact erases_session _
    | with_reducible exact erases_modifyPeer _ _
    | with_reducible exact erases_create _
    | with_reducible exact erases_mac _ _
    | with_reducible exact erases_send _ _
    | with_reducible exact erases_derived _
    | with_reducible exact erases_traversal _
    | with_reducible exact erases_sent _
    | with_reducible exact erases_cookie _ _
    | with_reducible exact erases_initiation _
    | with_reducible exact erases_response _
    | with_reducible exact erases_endpoint _ _
    | with_reducible exact erases_complete _
    | with_reducible exact erases_keepalive _
    | with_reducible exact erases_received _
    | with_reducible exact erases_put _
    | with_reducible exact erases_cookieConsume _
    | with_reducible exact afterMac_erases _ _ _ _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | with_reducible apply erases_if
    | split

theorem erases : ErasesStatePrefix observed receiveStep := by
  rw [← step_original]
  unfold observed stepWith
  repeat' first
    | with_reducible exact erases_step _
    | with_reducible exact erases_session _
    | with_reducible exact erases_modifyPeer _ _
    | with_reducible exact erases_create _
    | with_reducible exact erases_mac _ _
    | with_reducible exact erases_send _ _
    | with_reducible exact erases_derived _
    | with_reducible exact erases_traversal _
    | with_reducible exact erases_sent _
    | with_reducible exact erases_cookie _ _
    | with_reducible exact erases_initiation _
    | with_reducible exact erases_response _
    | with_reducible exact erases_endpoint _ _
    | with_reducible exact erases_complete _
    | with_reducible exact erases_keepalive _
    | with_reducible exact erases_received _
    | with_reducible exact erases_put _
    | with_reducible exact erases_cookieConsume _
    | with_reducible exact reception_erases _ _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | with_reducible apply erases_if
    | split

end Leanux.Proofs.WG.HandshakeSecurity.Worker
