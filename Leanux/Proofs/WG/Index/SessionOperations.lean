import Leanux.WG.Handshake

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- The unchanged original suffix after a successful keypair allocation. -/
def sessionAfterAllocation (pid : PeerId) (st : Nat) (kp : KeypairId) : WG.M Bool := do
  let p ← getPeer pid
  let initiator := st == HANDSHAKE_CONSUMED_RESPONSE
  setKeypair kp { (← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex := p.remoteIndex }
  if ← branch .sessionInitiator initiator then deriveKeys kp true p.chainingKey
  else deriveKeys kp false p.chainingKey
  handshakeZero pid
  if ← branch .sessionAlive !(← getPeer pid).isDead then
    addNewKeypair pid kp
    _ ← IndexOwner.peerDeref (.handshake pid)
    if !(← indexReplaceHandshake pid kp) then unsupported "begin_session: the handshake entry was unhashed"
    return true
  unsupported "a dead peer finishing a session"

def sessionAfterCreate (pid : PeerId) (st : Nat) (created : Option KeypairId) : WG.M Bool := do
  if ← branch .sessionNoKeypair created.isNone then return false
  let some kp := created | invariant "unreachable"
  sessionAfterAllocation pid st kp

theorem beginSession_owner_source (pid : PeerId) :
    beginSession pid = (do
      let st := (← getPeer pid).handshakeState
      if ← WG.andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
          (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE)) then return false
      let created ← keypairCreate (← IndexOwner.peerWord (.handshake pid))
      sessionAfterCreate pid st created) := rfl

end Leanux.Proofs.WG.Index
