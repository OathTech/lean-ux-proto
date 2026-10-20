import Leanux.Proofs.WG.HandshakeSecurity.ExchangeSessionEffects
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverHistory

/-! The slot-placement obligation is a local H1 rotation contract. Its state
premises are ordinary C1 slot bounds and nullable configured self-identity;
there is no initialized history or replay-security premise in this package. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

namespace Exchange

/-- The three role-dependent slots after H1 rotation, ordered current, previous,
next. This is the projection needed by T4; index-row uniqueness is separate. -/
def sessionSlots (p : Peer) (slot : KeypairId) :
    Option KeypairId × Option KeypairId × Option KeypairId :=
  if p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE then
    (some slot,if p.keypairNext.isSome then p.keypairNext else p.keypairCurrent,none)
  else (p.keypairCurrent,none,some slot)

def peerSlots (p : Peer) := (p.keypairCurrent,p.keypairPrevious,p.keypairNext)

def FreshSessionSlot (p : Peer) (slot : KeypairId) : Prop :=
  p.keypairCurrent ≠ some slot ∧ p.keypairPrevious ≠ some slot ∧ p.keypairNext ≠ some slot

/-- The session's actual new allocation remains resident at the final native
return and the caller has H1's role-dependent slots. A wire index or a counter
delta alone is not used as a keypair identity. -/
def SessionPlaced (pid : PeerId) (r : WGRunWitness Bool) : Prop :=
  ∃ before peer after caller key,
    r.before.dev = some before ∧ before.peers[pid]? = some peer ∧
    r.after.dev = some after ∧ after.peers[pid]? = some caller ∧
    after.keypairs[before.nextKeypairId]? = some key ∧
    key.internalId = r.before.keypairCounter + 1 ∧ key.peer = some pid ∧ key.refcount = 1 ∧
    key.iAmTheInitiator = (peer.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) ∧
    peerSlots caller = sessionSlots peer before.nextKeypairId

end Exchange

/-- Required local consequence of C2 H1 at `be8c209c`:
`Noise.beginSession_effect`, `Noise.rotationRun_excluded_key` and
`Noise.rotationRun_peer`. `Index.sessionEffect_installed` uses these same facts
for its resident key and role-selected slot; its additional final
`DeviceTablesSafe` premise is used for index-row uniqueness, which is absent
here. The guard below excludes the fresh slot from all three old slots and is
stronger than C2's release-list-only `Index.SessionRotationFresh`.

This remains an unconstructed native-call hypothesis after C2 landed: its
complete material and final role-slot projection still needs a bridge proof.
It assumes no initialized installation, exchange identity or event history. -/
structure H1SessionPlacement : Prop where
  session : ∀ (pid : PeerId) (r : WGRunWitness Bool) (device : Device) (peer : Peer),
    r.before.dev = some device → device.peers[pid]? = some peer →
    ConfiguredIdentity.Self peer.handshakeEntryPeer pid →
    Exchange.FreshSessionSlot peer device.nextKeypairId →
    r.Valid (beginSession pid) → r.value = true → Exchange.SessionPlaced pid r

namespace Exchange

theorem slot_fresh_of_current_slots (w : WGWorld) (d : Device) (pid : PeerId) (p : Peer)
    (safe : CurrentSlots.Inv w) (device : w.dev = some d) (resident : d.peers[pid]? = some p) :
    FreshSessionSlot p d.nextKeypairId := by
  have bound (kid : KeypairId)
      (slot : p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid) :
      kid < d.nextKeypairId := by
    exact (safe (Affiliation.state d) (by simp [Affiliation.view,device]) pid
      (Affiliation.peerCell p) kid (by simp [Affiliation.state,resident]) slot).1
  refine ⟨?_,?_,?_⟩
  · intro same; exact Nat.lt_irrefl _ (bound _ (Or.inl same))
  · intro same; exact Nat.lt_irrefl _ (bound _ (Or.inr (Or.inl same)))
  · intro same; exact Nat.lt_irrefl _ (bound _ (Or.inr (Or.inr same)))

theorem session_placed (rotation : H1SessionPlacement) (pid : PeerId)
    (r : WGRunWitness Bool) (valid : r.Valid (beginSession pid)) (success : r.value = true)
    (configured : ConfiguredIdentity.Inv r.before) (slots : CurrentSlots.Inv r.before) :
    SessionPlaced pid r := by
  obtain ⟨context,middle,clock,front,_⟩ := session_true_front pid r.before r.after r.ambientBefore r.ambientAfter
    (by simpa only [WGRunWitness.Valid,success] using valid)
  obtain ⟨device,key,present,resident,_⟩ := Origins.front_effect pid context r.before middle
    r.ambientBefore clock front
  have self := (configured (ConfiguredIdentity.state device)
    (by simp [ConfiguredIdentity.view,present])).self pid (ConfiguredIdentity.cell context.peer)
      (by simp [ConfiguredIdentity.state,resident])
  exact rotation.session pid r device context.peer present resident self
    (slot_fresh_of_current_slots _ _ _ _ slots present resident) valid success

end Exchange
end Leanux.Proofs.WG.HandshakeSecurity
