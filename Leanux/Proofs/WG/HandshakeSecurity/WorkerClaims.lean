import Leanux.Proofs.WG.HandshakeSecurity.WorkerObservation

/-! Timestamp receipts retain their native write evidence and strict increase
through every branch of the original receive worker, including a later Stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Worker
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Origins.HandshakeSources

private theorem silent {α : Type} (action : WG.M α) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ h => h) (fun _ _ _ _ _ _ h _ => h)

private theorem safe_step {α : Type} (a : WG.M α) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.step a) := silent _

private theorem safe_session (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.session pid) := silent _

private theorem safe_modifyPeer (pid : PeerId) (f : Peer → Peer) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.modifyPeer pid f) := silent _

private theorem safe_create (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.create pid) := silent _

private theorem safe_mac (pid : PeerId) (msg : List UInt8) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.mac pid msg) := silent _

private theorem safe_send (pid : PeerId) (msg : List UInt8) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.send pid msg) := silent _

private theorem safe_derived (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.derived pid) := silent _

private theorem safe_traversal (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.traversal pid) := silent _

private theorem safe_sent (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.sent pid) := silent _

private theorem safe_cookie (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.cookie msg src) := silent _

private theorem safe_initiation (msg : List UInt8) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.initiation msg) := consume_increasing msg

private theorem safe_response (msg : List UInt8) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.response msg) := silent _

private theorem safe_endpoint (pid : PeerId) (src : SkbSource) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.endpoint pid src) := silent _

private theorem safe_complete (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.complete pid) := silent _

private theorem safe_keepalive (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.keepalive pid) := silent _

private theorem safe_received (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.received pid) := silent _

private theorem safe_put (peer : Option PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.put peer) := silent _

private theorem safe_cookieConsume (msg : List UInt8) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (ops.cookieConsume msg) := silent _

private theorem safe_pure {α : Type} (x : α) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (pure x : WGPrefix TimestampReceipt α) :=
  StatePrefixEnsures.pure x (fun _ _ _ h => h) (fun _ _ _ h => h)

private theorem safe_if {α : Type} (c : Prop) [Decidable c]
    (x y : WGPrefix TimestampReceipt α)
    (hx : StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts x)
    (hy : StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts y) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (if c then x else y) := by
  split <;> assumption

private theorem response_safe (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (responseWith ops pid) := by
  unfold responseWith
  repeat' first
    | with_reducible exact safe_step _
    | with_reducible exact safe_session _
    | with_reducible exact safe_modifyPeer _ _
    | with_reducible exact safe_create _
    | with_reducible exact safe_mac _ _
    | with_reducible exact safe_send _ _
    | with_reducible exact safe_derived _
    | with_reducible exact safe_traversal _
    | with_reducible exact safe_sent _
    | with_reducible exact safe_cookie _ _
    | with_reducible exact safe_initiation _
    | with_reducible exact safe_response _
    | with_reducible exact safe_endpoint _ _
    | with_reducible exact safe_complete _
    | with_reducible exact safe_keepalive _
    | with_reducible exact safe_received _
    | with_reducible exact safe_put _
    | with_reducible exact safe_cookieConsume _
    | with_reducible exact safe_pure _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | with_reducible apply safe_if
    | split

private theorem afterMac_safe (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (afterMacWith ops msg src loaded mac) := by
  unfold afterMacWith
  repeat' first
    | with_reducible exact safe_step _
    | with_reducible exact safe_session _
    | with_reducible exact safe_modifyPeer _ _
    | with_reducible exact safe_create _
    | with_reducible exact safe_mac _ _
    | with_reducible exact safe_send _ _
    | with_reducible exact safe_derived _
    | with_reducible exact safe_traversal _
    | with_reducible exact safe_sent _
    | with_reducible exact safe_cookie _ _
    | with_reducible exact safe_initiation _
    | with_reducible exact safe_response _
    | with_reducible exact safe_endpoint _ _
    | with_reducible exact safe_complete _
    | with_reducible exact safe_keepalive _
    | with_reducible exact safe_received _
    | with_reducible exact safe_put _
    | with_reducible exact safe_cookieConsume _
    | with_reducible exact response_safe _
    | with_reducible exact safe_pure _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | with_reducible apply safe_if
    | split

private theorem reception_safe (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (receptionWith ops msg src) := by
  unfold receptionWith
  repeat' first
    | with_reducible exact safe_step _
    | with_reducible exact safe_session _
    | with_reducible exact safe_modifyPeer _ _
    | with_reducible exact safe_create _
    | with_reducible exact safe_mac _ _
    | with_reducible exact safe_send _ _
    | with_reducible exact safe_derived _
    | with_reducible exact safe_traversal _
    | with_reducible exact safe_sent _
    | with_reducible exact safe_cookie _ _
    | with_reducible exact safe_initiation _
    | with_reducible exact safe_response _
    | with_reducible exact safe_endpoint _ _
    | with_reducible exact safe_complete _
    | with_reducible exact safe_keepalive _
    | with_reducible exact safe_received _
    | with_reducible exact safe_put _
    | with_reducible exact safe_cookieConsume _
    | with_reducible exact afterMac_safe _ _ _ _
    | with_reducible exact safe_pure _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | with_reducible apply safe_if
    | split

theorem increasing  :
    StatePrefixPreserves (fun h _ _ => IncreasingReceipts h) IncreasingReceipts
      (observed) := by
  unfold observed stepWith
  repeat' first
    | with_reducible exact safe_step _
    | with_reducible exact safe_session _
    | with_reducible exact safe_modifyPeer _ _
    | with_reducible exact safe_create _
    | with_reducible exact safe_mac _ _
    | with_reducible exact safe_send _ _
    | with_reducible exact safe_derived _
    | with_reducible exact safe_traversal _
    | with_reducible exact safe_sent _
    | with_reducible exact safe_cookie _ _
    | with_reducible exact safe_initiation _
    | with_reducible exact safe_response _
    | with_reducible exact safe_endpoint _ _
    | with_reducible exact safe_complete _
    | with_reducible exact safe_keepalive _
    | with_reducible exact safe_received _
    | with_reducible exact safe_put _
    | with_reducible exact safe_cookieConsume _
    | with_reducible exact reception_safe _ _
    | with_reducible exact safe_pure _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | with_reducible apply safe_if
    | split

end Leanux.Proofs.WG.HandshakeSecurity.Worker
