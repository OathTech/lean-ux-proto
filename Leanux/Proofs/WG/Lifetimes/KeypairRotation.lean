import Leanux.Proofs.WG.Lifetimes.AllocationAmbient

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Original keypair rotation and confirmation with resolved-store accesses.
Scalar keypair slots may alias. Their ownership and reference integrity are
not premises or conclusions of these access-safety contracts. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

namespace AmbientContracts

theorem getPeer_frame (c : AmbientContracts I) (P : IdentityView → Prop) (id : PeerId) :
    AmbientSpec I P (getPeerMixed id) (fun _ => P) :=
  forget (c.getPeer P id) (fun _ _ hi => hi.1)

theorem unsupported (c : AmbientContracts I) (P : IdentityView → Prop) (why : String) :
    AmbientSpec I P (liftPrefix (Leanux.unsupported (α := α) why)) (fun _ => P) := by
  apply c.kernel
  intro w x v hr
  simp [Leanux.unsupported] at hr

end AmbientContracts

def addNewKeypairPrefix (pid : PeerId) (newKeypair : KeypairId) : MixedM Unit := do
  let p ← getPeerMixed pid
  let (previous, next, current) := (p.keypairPrevious, p.keypairNext, p.keypairCurrent)
  if ← liftPrefix (branch .addKeypairInitiator (← getKeypairPrefix newKeypair).iAmTheInitiator) then
    if ← liftPrefix (branch .addKeypairHasNext next.isSome) then
      modifyPeerKeysPrefix pid fun p => {p with keypairNext := none, keypairPrevious := next}
      keypairPutPrefix current true
    else
      modifyPeerKeysPrefix pid fun p => {p with keypairPrevious := current}
    keypairPutPrefix previous true
    modifyPeerKeysPrefix pid fun p => {p with keypairCurrent := some newKeypair}
  else
    modifyPeerKeysPrefix pid fun p => {p with keypairNext := some newKeypair}
    keypairPutPrefix next true
    modifyPeerKeysPrefix pid fun p => {p with keypairPrevious := none}
    keypairPutPrefix previous true

def receivedWithKeypairPrefix (pid : PeerId) (received : KeypairId) : MixedM Bool := do
  if ← liftPrefix (branch .receivedNotNew ((← getPeerMixed pid).keypairNext != some received)) then return false
  if ← liftPrefix (branch .receivedChanged ((← getPeerMixed pid).keypairNext != some received)) then return false
  let p ← getPeerMixed pid
  let old := p.keypairPrevious
  modifyPeerKeysPrefix pid fun p => {p with keypairPrevious := p.keypairCurrent}
  keypairPutPrefix old true
  modifyPeerKeysPrefix pid fun p => {p with keypairCurrent := some received, keypairNext := none}
  return true

theorem addNewKeypairPrefix_erases (pid : PeerId) (kp : KeypairId) :
    ErasesPrefix (addNewKeypairPrefix pid kp) (addNewKeypair pid kp) := by
  unfold addNewKeypairPrefix addNewKeypair
  repeat' first
    | exact getPeerMixed_erases _
    | exact getKeypairPrefix_erases _
    | exact modifyPeerKeysPrefix_erases _ _
    | exact keypairPutPrefix_erases _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | intro x
    | split
    | rfl

theorem receivedWithKeypairPrefix_erases (pid : PeerId) (kp : KeypairId) :
    ErasesPrefix (receivedWithKeypairPrefix pid kp) (receivedWithKeypair pid kp) := by
  unfold receivedWithKeypairPrefix receivedWithKeypair
  repeat' first
    | exact getPeerMixed_erases _
    | exact modifyPeerKeysPrefix_erases _ _
    | exact keypairPutPrefix_erases _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | intro x
    | split
    | rfl

theorem addNewKeypairPrefix_preserves_ambient (c : AmbientContracts I)
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now))
    (pid : PeerId) (kp : KeypairId) :
    PrefixPreserves I LifetimeEvent.Safe (addNewKeypairPrefix pid kp) := by
  unfold addNewKeypairPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro p
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getKeypair (fun _ => True) kp))
  intro k
  apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro initiator
  split
  · have tail : PrefixPreserves I LifetimeEvent.Safe
        (do keypairPutPrefix p.keypairPrevious true
            modifyPeerKeysPrefix pid fun q => {q with keypairCurrent := some kp}) := by
      apply PrefixPreserves.bind (put p.keypairPrevious true)
      intro _
      exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun q => {q with keypairCurrent := some kp}) (fun _ => rfl))
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro hasNext
    split
    · apply PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun q => {q with keypairNext := none, keypairPrevious := p.keypairNext}) (fun _ => rfl)))
      intro _
      apply PrefixPreserves.bind (put p.keypairCurrent true)
      intro _
      exact tail
    · apply PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun q => {q with keypairPrevious := p.keypairCurrent}) (fun _ => rfl)))
      intro _
      exact tail
  · apply PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
      (fun q => {q with keypairNext := some kp}) (fun _ => rfl)))
    intro _
    apply PrefixPreserves.bind (put p.keypairNext true)
    intro _
    apply PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
      (fun q => {q with keypairPrevious := none}) (fun _ => rfl)))
    intro _
    exact put p.keypairPrevious true

theorem receivedWithKeypairPrefix_preserves_ambient (c : AmbientContracts I)
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now))
    (pid : PeerId) (kp : KeypairId) :
    PrefixPreserves I LifetimeEvent.Safe (receivedWithKeypairPrefix pid kp) := by
  unfold receivedWithKeypairPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro first
  apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro notNew
  split
  · exact PrefixPreserves.pure c.safe false
  · apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
    intro second
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro changed
    split
    · exact PrefixPreserves.pure c.safe false
    · apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
      intro p
      apply PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun q => {q with keypairPrevious := q.keypairCurrent}) (fun _ => rfl)))
      intro _
      apply PrefixPreserves.bind (put p.keypairPrevious true)
      intro _
      apply PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun q => {q with keypairCurrent := some kp, keypairNext := none}) (fun _ => rfl)))
      intro _
      exact PrefixPreserves.pure c.safe true

theorem addNewKeypairPrefix_allocation (pid : PeerId) (kp : KeypairId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (addNewKeypairPrefix pid kp) :=
  addNewKeypairPrefix_preserves_ambient allocationAmbient keypairPutPrefix_allocation pid kp

theorem receivedWithKeypairPrefix_allocation (pid : PeerId) (kp : KeypairId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (receivedWithKeypairPrefix pid kp) :=
  receivedWithKeypairPrefix_preserves_ambient allocationAmbient keypairPutPrefix_allocation pid kp

end Leanux.Proofs.WG.Lifetimes
