import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerParametric
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects

/-! Lexical causes wrap the actual handshake callbacks, while the existing
consumer and completed-exchange observers remain the supplied source. Only the
two timer-producing helper bodies need effect callbacks of their own. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources

/-- Replace only the two native helpers that can create timers. The caller can
first decorate consumer/create callbacks with completed exchange receipts. -/
def withEffects (base : Ops (WGPrefix E)) (record : HandshakeCausal.Event → E)
    (effects : TimerEffects.Ops (WGPrefix E)) : Ops (WGPrefix E) :=
  {base with
    derived := fun pid => HandshakeWorker.callback record .sessionDerived pid
      (TimerEffects.derivedWith effects pid)
    traversal := fun pid => HandshakeWorker.callback record .traversal pid
      (TimerEffects.traversalWith effects pid)}

/-- Every protected callback has its own occurrence token in the full journal.
Entry is not an authentication assertion; the callback's existing admission
receipt and initialized history still have to justify that occurrence. -/
def scopeOps (record : CausalScope.Event Cause → E)
    (cause : HandshakeCausal.Kind → PeerId → Cause) (base : Ops (WGPrefix E)) :
    Ops (WGPrefix E) :=
  {base with
    session := fun pid => CausalScope.scope record (cause .session pid) (base.session pid)
    modifyPeer := fun pid f => CausalScope.scope record (cause .peerWrite pid) (base.modifyPeer pid f)
    create := fun pid => CausalScope.scope record (cause .responseCreate pid) (base.create pid)
    mac := fun pid msg => CausalScope.scope record (cause .outgoingMac pid) (base.mac pid msg)
    send := fun pid msg => CausalScope.scope record (cause .send pid) (base.send pid msg)
    derived := fun pid => CausalScope.scope record (cause .sessionDerived pid) (base.derived pid)
    traversal := fun pid => CausalScope.scope record (cause .traversal pid) (base.traversal pid)
    sent := fun pid => CausalScope.scope record (cause .authenticatedSent pid) (base.sent pid)
    endpoint := fun pid src => CausalScope.scope record (cause .endpoint pid) (base.endpoint pid src)
    complete := fun pid => CausalScope.scope record (cause .handshakeComplete pid) (base.complete pid)
    keepalive := fun pid => CausalScope.scope record (cause .keepalive pid) (base.keepalive pid)
    received := fun pid => CausalScope.scope record (cause .authenticatedReceived pid) (base.received pid)}

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
