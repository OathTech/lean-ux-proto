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
    AmbientSpec I P (liftWGPrefix (Leanux.unsupported (α := α) why)) (fun _ => P) := by
  apply c.store
  intro initial
  exact hoare_liftAmbient (AmbientM.unsupported why) (fun w => wgStoreView w = initial)

end AmbientContracts

namespace ProductAmbientContracts

theorem getPeer_frame (c : ProductAmbientContracts I) (P : IdentityView → Prop) (id : PeerId) :
    ProductAmbientSpec I P (liftWGObserver (getPeerMixed id)) (fun _ => P) :=
  forget (c.getPeer P id) (fun _ _ hi => hi.1)

theorem unsupported (c : ProductAmbientContracts I) (P : IdentityView → Prop) (why : String) :
    ProductAmbientSpec I P (liftPrefix (Leanux.unsupported (α := α) why)) (fun _ => P) :=
  c.ambient P (AmbientM.unsupported why)

end ProductAmbientContracts

def addNewKeypairPrefix (pid : PeerId) (newKeypair : KeypairId) : MixedM Unit := do
  let p ← getPeerMixed pid
  let (previous, next, current) := (p.keypairPrevious, p.keypairNext, p.keypairCurrent)
  if ← liftWGPrefix (branch .addKeypairInitiator (← getKeypairPrefix newKeypair).iAmTheInitiator) then
    if ← liftWGPrefix (branch .addKeypairHasNext next.isSome) then
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
  if ← liftWGPrefix (branch .receivedNotNew ((← getPeerMixed pid).keypairNext != some received)) then return false
  if ← liftWGPrefix (branch .receivedChanged ((← getPeerMixed pid).keypairNext != some received)) then return false
  let p ← getPeerMixed pid
  let old := p.keypairPrevious
  modifyPeerKeysPrefix pid fun p => {p with keypairPrevious := p.keypairCurrent}
  keypairPutPrefix old true
  modifyPeerKeysPrefix pid fun p => {p with keypairCurrent := some received, keypairNext := none}
  return true

theorem addNewKeypairPrefix_erases (pid : PeerId) (kp : KeypairId) :
    ErasesStatePrefix (addNewKeypairPrefix pid kp) (addNewKeypair pid kp) := by
  unfold addNewKeypairPrefix addNewKeypair
  apply erasesStatePrefix_bind (getPeerMixed_erases pid)
  intro p
  dsimp only
  apply erasesStatePrefix_bind (getKeypairPrefix_erases kp)
  intro k
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro initiator
  split
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro hasNext
    split
    · apply erasesStatePrefix_bind (modifyPeerKeysPrefix_erases _ _)
      intro _
      apply erasesStatePrefix_bind (keypairPutPrefix_erases _ _)
      intro _
      apply erasesStatePrefix_bind (keypairPutPrefix_erases _ _)
      intro _
      exact modifyPeerKeysPrefix_erases _ _
    · apply erasesStatePrefix_bind (modifyPeerKeysPrefix_erases _ _)
      intro _
      apply erasesStatePrefix_bind (keypairPutPrefix_erases _ _)
      intro _
      exact modifyPeerKeysPrefix_erases _ _
  · apply erasesStatePrefix_bind (modifyPeerKeysPrefix_erases _ _)
    intro _
    apply erasesStatePrefix_bind (keypairPutPrefix_erases _ _)
    intro _
    apply erasesStatePrefix_bind (modifyPeerKeysPrefix_erases _ _)
    intro _
    exact keypairPutPrefix_erases _ _

theorem receivedWithKeypairPrefix_erases (pid : PeerId) (kp : KeypairId) :
    ErasesStatePrefix (receivedWithKeypairPrefix pid kp) (receivedWithKeypair pid kp) := by
  unfold receivedWithKeypairPrefix receivedWithKeypair
  apply erasesStatePrefix_bind (getPeerMixed_erases pid)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro notNew
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (getPeerMixed_erases pid)
    intro p
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro changed
    split
    · exact erasesStatePrefix_pure _
    · apply erasesStatePrefix_bind (getPeerMixed_erases pid)
      intro p
      apply erasesStatePrefix_bind (modifyPeerKeysPrefix_erases _ _)
      intro _
      apply erasesStatePrefix_bind (keypairPutPrefix_erases _ _)
      intro _
      apply erasesStatePrefix_bind (modifyPeerKeysPrefix_erases _ _)
      intro _
      exact erasesStatePrefix_pure _

theorem addNewKeypairPrefix_preserves_ambient (c : AmbientContracts I)
    (put : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now))
    (pid : PeerId) (kp : KeypairId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (addNewKeypairPrefix pid kp) := by
  unfold addNewKeypairPrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro p
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getKeypair (fun _ => True) kp))
  intro k
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro initiator
  split
  · have tail : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
        (do keypairPutPrefix p.keypairPrevious true
            modifyPeerKeysPrefix pid fun q => {q with keypairCurrent := some kp}) := by
      apply StatePrefixEnsures.bind (put p.keypairPrevious true)
      intro _
      exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun q => {q with keypairCurrent := some kp}) (fun _ => rfl))
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro hasNext
    split
    · apply StatePrefixEnsures.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun q => {q with keypairNext := none, keypairPrevious := p.keypairNext}) (fun _ => rfl)))
      intro _
      apply StatePrefixEnsures.bind (put p.keypairCurrent true)
      intro _
      exact tail
    · apply StatePrefixEnsures.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun q => {q with keypairPrevious := p.keypairCurrent}) (fun _ => rfl)))
      intro _
      exact tail
  · apply StatePrefixEnsures.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
      (fun q => {q with keypairNext := some kp}) (fun _ => rfl)))
    intro _
    apply StatePrefixEnsures.bind (put p.keypairNext true)
    intro _
    apply StatePrefixEnsures.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
      (fun q => {q with keypairPrevious := none}) (fun _ => rfl)))
    intro _
    exact put p.keypairPrevious true

theorem receivedWithKeypairPrefix_preserves_ambient (c : AmbientContracts I)
    (put : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now))
    (pid : PeerId) (kp : KeypairId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (receivedWithKeypairPrefix pid kp) := by
  unfold receivedWithKeypairPrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro first
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro notNew
  split
  · exact StatePrefixEnsures.pure false (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
  · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
    intro second
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro changed
    split
    · exact StatePrefixEnsures.pure false (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
      intro p
      apply StatePrefixEnsures.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun q => {q with keypairPrevious := q.keypairCurrent}) (fun _ => rfl)))
      intro _
      apply StatePrefixEnsures.bind (put p.keypairPrevious true)
      intro _
      apply StatePrefixEnsures.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun q => {q with keypairCurrent := some kp, keypairNext := none}) (fun _ => rfl)))
      intro _
      exact StatePrefixEnsures.pure true (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)

theorem addNewKeypairPrefix_preserves_product (c : ProductAmbientContracts I)
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now)))
    (pid : PeerId) (kp : KeypairId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (addNewKeypairPrefix pid kp)) := by
  have branch_spec (d : Decision) (b : Bool) :
      ProductAmbientSpec I (fun _ => True) (liftWGObserver (liftWGPrefix (Leanux.branch d b)))
        (fun _ _ => True) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  simp only [addNewKeypairPrefix, liftWGObserver_bind]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro p
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getKeypair (fun _ => True) kp))
  intro k
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
  intro initiator
  split
  · simp only [liftWGObserver_bind]
    have tail : PrefixPreserves I LifetimeEvent.Safe
        (do liftWGObserver (keypairPutPrefix p.keypairPrevious true)
            liftWGObserver (modifyPeerKeysPrefix pid fun q => {q with keypairCurrent := some kp})) := by
      apply PrefixPreserves.bind (put p.keypairPrevious true)
      intro _
      exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
        (fun q => {q with keypairCurrent := some kp}) (fun _ => rfl))
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
    intro hasNext
    split
    · simp only [liftWGObserver_bind]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
        (fun q => {q with keypairNext := none, keypairPrevious := p.keypairNext}) (fun _ => rfl)))
      intro _
      apply PrefixPreserves.bind (put p.keypairCurrent true)
      intro _
      exact tail
    · simp only [liftWGObserver_bind]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
        (fun q => {q with keypairPrevious := p.keypairCurrent}) (fun _ => rfl)))
      intro _
      exact tail
  · simp only [liftWGObserver_bind]
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
      (fun q => {q with keypairNext := some kp}) (fun _ => rfl)))
    intro _
    apply PrefixPreserves.bind (put p.keypairNext true)
    intro _
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
      (fun q => {q with keypairPrevious := none}) (fun _ => rfl)))
    intro _
    exact put p.keypairPrevious true

theorem receivedWithKeypairPrefix_preserves_product (c : ProductAmbientContracts I)
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now)))
    (pid : PeerId) (kp : KeypairId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (receivedWithKeypairPrefix pid kp)) := by
  have branch_spec (d : Decision) (b : Bool) :
      ProductAmbientSpec I (fun _ => True) (liftWGObserver (liftWGPrefix (Leanux.branch d b)))
        (fun _ _ => True) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  simp only [receivedWithKeypairPrefix, liftWGObserver_bind]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro first
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
  intro notNew
  split
  · simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe false
  · simp only [liftWGObserver_bind]
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer (fun _ => True) pid))
    intro second
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec _ _))
    intro changed
    split
    · simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe false
    · simp only [liftWGObserver_bind, liftWGObserver_pure]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer (fun _ => True) pid))
      intro p
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
        (fun q => {q with keypairPrevious := q.keypairCurrent}) (fun _ => rfl)))
      intro _
      apply PrefixPreserves.bind (put p.keypairPrevious true)
      intro _
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
        (fun q => {q with keypairCurrent := some kp, keypairNext := none}) (fun _ => rfl)))
      intro _
      simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe true

theorem addNewKeypairPrefix_allocation (pid : PeerId) (kp : KeypairId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (addNewKeypairPrefix pid kp) :=
  addNewKeypairPrefix_preserves_ambient allocationAmbient keypairPutPrefix_allocation pid kp

theorem receivedWithKeypairPrefix_allocation (pid : PeerId) (kp : KeypairId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (receivedWithKeypairPrefix pid kp) :=
  receivedWithKeypairPrefix_preserves_ambient allocationAmbient keypairPutPrefix_allocation pid kp

end Leanux.Proofs.WG.Lifetimes
