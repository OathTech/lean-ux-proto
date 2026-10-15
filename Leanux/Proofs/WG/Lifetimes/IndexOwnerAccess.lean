import Leanux.Proofs.WG.Lifetimes.Ambient

/-! Resolved accesses to the single embedded index-entry peer word. The owner
is read again by the setter, after any intervening acquisition. Dereference
checks that word for NULL; it does not resolve the peer named by the word. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def peerWordPrefix : IndexOwner → MixedM (Option PeerId)
  | .handshake pid => return (← getPeerMixed pid).handshakeEntryPeer
  | .keypair kp => return (← getKeypairPrefix kp).peer

def setPeerWordPrefix (owner : IndexOwner) (peer : Option PeerId) : MixedM Unit := do
  match owner with
  | .handshake pid => setPeerMixed pid { (← getPeerMixed pid) with handshakeEntryPeer := peer }
  | .keypair kp => setKeypairPrefix kp { (← getKeypairPrefix kp) with peer }

def peerDerefPrefix (owner : IndexOwner) : MixedM PeerId := do
  let some pid ← peerWordPrefix owner |
    liftPrefix (unsupported "entry->peer is NULL: the C dereferences it")
  return pid

theorem peerWordPrefix_erases (owner : IndexOwner) :
    ErasesPrefix (peerWordPrefix owner) owner.peerWord := by
  cases owner <;> unfold peerWordPrefix IndexOwner.peerWord
  all_goals apply erasesPrefix_bind
  all_goals first
    | exact getPeerMixed_erases _
    | exact getKeypairPrefix_erases _
    | intro x; exact erasesPrefix_pure _

theorem setPeerWordPrefix_erases (owner : IndexOwner) (peer : Option PeerId) :
    ErasesPrefix (setPeerWordPrefix owner peer) (owner.setPeerWord peer) := by
  cases owner <;> unfold setPeerWordPrefix IndexOwner.setPeerWord
  all_goals apply erasesPrefix_bind
  all_goals first
    | exact getPeerMixed_erases _
    | exact getKeypairPrefix_erases _
    | intro x; exact setPeerMixed_erases _ _
    | intro x; exact setKeypairPrefix_erases _ _

theorem peerDerefPrefix_erases (owner : IndexOwner) :
    ErasesPrefix (peerDerefPrefix owner) owner.peerDeref := by
  unfold peerDerefPrefix IndexOwner.peerDeref
  apply erasesPrefix_bind (peerWordPrefix_erases owner)
  intro peer
  cases peer
  · exact erasesPrefix_lift _
  · exact erasesPrefix_pure _

theorem peerWordPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (owner : IndexOwner) : AmbientSpec I P (peerWordPrefix owner) (fun _ => P) := by
  cases owner with
  | handshake pid =>
    apply PrefixEnsures.bind (c.getPeer P pid)
    intro p
    exact AmbientContracts.forget (c.pure (fun s => P s ∧ s.1.slots pid = some p.internalId) p.handshakeEntryPeer)
      (fun _ _ h => h.1)
  | keypair kp =>
    apply PrefixEnsures.bind (c.getKeypair P kp)
    intro k
    exact AmbientContracts.forget (c.pure (fun s => P s ∧ s.2.1 kp = some k.internalId) k.peer)
      (fun _ _ h => h.1)

theorem setPeerWordPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (owner : IndexOwner) (peer : Option PeerId) :
    AmbientSpec I P (setPeerWordPrefix owner peer) (fun _ => P) := by
  cases owner with
  | handshake pid =>
    apply PrefixEnsures.bind (c.getPeer P pid)
    intro p
    exact c.setPeer P pid {p with handshakeEntryPeer := peer}
  | keypair kp =>
    apply PrefixEnsures.bind (c.getKeypair P kp)
    intro k
    exact c.setKeypair P kp {k with peer}

theorem peerDerefPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (owner : IndexOwner) : AmbientSpec I P (peerDerefPrefix owner) (fun _ => P) := by
  unfold peerDerefPrefix
  apply PrefixEnsures.bind (peerWordPrefix_spec c P owner)
  intro peer
  cases peer with
  | none =>
    apply c.kernel
    intro w x v hr
    simp [unsupported] at hr
  | some pid => exact c.pure P pid

end Leanux.Proofs.WG.Lifetimes
