import Leanux.Proofs.WG.Lifetimes.KeypairRelease
import Leanux.Proofs.WG.Lifetimes.PacketRelease
import Leanux.Proofs.WG.Lifetimes.ReleaseAmbient

/-! The complete keypair-clear caller and finite sequences of the listed
reference/free calls. Allocation, device teardown and scheduler closure are
separate obligations. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged

def modifyPeerKeysPrefix (pid : PeerId) (f : Peer → Peer) : MixedM Unit := do
  setPeerMixed pid (f (← getPeerMixed pid))

theorem modifyPeerKeysPrefix_erases (pid : PeerId) (f : Peer → Peer) :
    ErasesPrefix (modifyPeerKeysPrefix pid f) (do setPeer pid (f (← getPeer pid))) :=
  erasesPrefix_bind (getPeerMixed_erases pid) (fun p => setPeerMixed_erases pid (f p))

theorem modifyPeerKeysPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) (f : Peer → Peer)
    (hf : ∀ p, (f p).internalId = p.internalId) :
    AmbientSpec I P (modifyPeerKeysPrefix pid f) (fun _ => P) := by
  apply PrefixEnsures.bind (c.getPeer P pid)
  intro p
  exact (c.setPeer P pid (f p)).consequence
    (fun _ _ hi => ⟨hi.1, hi.2.1, by simpa only [hf p] using hi.2.2⟩)
    (fun _ _ _ hi => hi)

theorem modifyPeerKeysPrefix_spec (P : IdentityView → Prop) (pid : PeerId) (f : Peer → Peer)
    (hf : ∀ p, (f p).internalId = p.internalId) :
    MixedSpec P (modifyPeerKeysPrefix pid f) (fun _ => P) :=
  modifyPeerKeysPrefix_spec_ambient mixedAmbient P pid f hf

def keypairsClearPrefix (pid : PeerId) : MixedM Unit := do
  let old := (← getPeerMixed pid).keypairNext
  modifyPeerKeysPrefix pid fun p => {p with keypairNext := none}
  keypairPutPrefix old true
  let old := (← getPeerMixed pid).keypairPrevious
  modifyPeerKeysPrefix pid fun p => {p with keypairPrevious := none}
  keypairPutPrefix old true
  let old := (← getPeerMixed pid).keypairCurrent
  modifyPeerKeysPrefix pid fun p => {p with keypairCurrent := none}
  keypairPutPrefix old true

theorem keypairsClearPrefix_erases (pid : PeerId) :
    ErasesPrefix (keypairsClearPrefix pid) (keypairsClear pid) := by
  unfold keypairsClearPrefix keypairsClear
  apply erasesPrefix_bind (getPeerMixed_erases pid)
  intro p
  apply erasesPrefix_bind (modifyPeerKeysPrefix_erases pid (fun p => {p with keypairNext := none}))
  intro _
  apply erasesPrefix_bind (keypairPutPrefix_erases p.keypairNext true)
  intro _
  apply erasesPrefix_bind (getPeerMixed_erases pid)
  intro p
  apply erasesPrefix_bind (modifyPeerKeysPrefix_erases pid (fun p => {p with keypairPrevious := none}))
  intro _
  apply erasesPrefix_bind (keypairPutPrefix_erases p.keypairPrevious true)
  intro _
  apply erasesPrefix_bind (getPeerMixed_erases pid)
  intro p
  apply erasesPrefix_bind (modifyPeerKeysPrefix_erases pid (fun p => {p with keypairCurrent := none}))
  intro _
  exact keypairPutPrefix_erases p.keypairCurrent true

theorem release_getPeer (pid : PeerId) :
    PrefixPreserves ReleaseInv LifetimeEvent.Safe (getPeerMixed pid) :=
  ((mixed_getPeer ReleaseUnique pid).consequence (fun _ _ hi => hi)
    (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)).preserves

theorem keypairsClearPrefix_preserves_ambient (c : AmbientContracts I)
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now))
    (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (keypairsClearPrefix pid) := by
  unfold keypairsClearPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro p
  apply PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
    (fun p => {p with keypairNext := none}) (fun _ => rfl)))
  intro _
  apply PrefixPreserves.bind (put p.keypairNext true)
  intro _
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro p
  apply PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
    (fun p => {p with keypairPrevious := none}) (fun _ => rfl)))
  intro _
  apply PrefixPreserves.bind (put p.keypairPrevious true)
  intro _
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro p
  apply PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
    (fun p => {p with keypairCurrent := none}) (fun _ => rfl)))
  intro _
  exact put p.keypairCurrent true

theorem keypairsClearPrefix_preserves (pid : PeerId) :
    PrefixPreserves ReleaseInv LifetimeEvent.Safe (keypairsClearPrefix pid) :=
  keypairsClearPrefix_preserves_ambient releaseAmbient keypairPutPrefix_preserves pid

/-- These constructors name complete original calls, not arbitrary mirror
steps. Acquisition's optional result is discarded only by this sequence API. -/
inductive ReleaseCall where
  | acquire (kp : Option KeypairId)
  | put (kp : Option KeypairId) (unreferenceNow : Bool)
  | freeTx (id : SkbId)
  | freeRx (id : SkbId)
  | clear (pid : PeerId)

namespace ReleaseCall

def original : ReleaseCall → M Unit
  | .acquire kp => do let _ ← keypairGet kp; pure ()
  | .put kp now => keypairPut kp now
  | .freeTx id => freeTxSkb id
  | .freeRx id => freeRxSkb id
  | .clear pid => keypairsClear pid

def observed : ReleaseCall → MixedM Unit
  | .acquire kp => do let _ ← keypairGetPrefix kp; pure ()
  | .put kp now => keypairPutPrefix kp now
  | .freeTx id => freeTxSkbPrefix id
  | .freeRx id => freeRxSkbPrefix id
  | .clear pid => keypairsClearPrefix pid

def execute : List ReleaseCall → M Unit
  | [] => pure ()
  | c :: cs => c.original >>= fun _ => execute cs

def observe : List ReleaseCall → MixedM Unit
  | [] => pure ()
  | c :: cs => c.observed >>= fun _ => observe cs

theorem erases (c : ReleaseCall) : ErasesPrefix c.observed c.original := by
  cases c with
  | acquire kp => exact erasesPrefix_bind (keypairGetPrefix_erases kp) (fun _ => erasesPrefix_pure ())
  | put kp now => exact keypairPutPrefix_erases kp now
  | freeTx id => exact freeTxSkbPrefix_erases id
  | freeRx id => exact freeRxSkbPrefix_erases id
  | clear pid => exact keypairsClearPrefix_erases pid

theorem preserves (c : ReleaseCall) : PrefixPreserves ReleaseInv LifetimeEvent.Safe c.observed := by
  cases c with
  | acquire kp =>
    exact PrefixPreserves.bind (keypairGetPrefix_preserves kp)
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) ())
  | put kp now => exact keypairPutPrefix_preserves kp now
  | freeTx id => exact freeTxSkbPrefix_preserves id
  | freeRx id => exact freeRxSkbPrefix_preserves id
  | clear pid => exact keypairsClearPrefix_preserves pid

theorem observe_erases (cs : List ReleaseCall) : ErasesPrefix (observe cs) (execute cs) := by
  induction cs with
  | nil => exact erasesPrefix_pure ()
  | cons c cs ih => exact erasesPrefix_bind c.erases (fun _ => ih)

theorem observe_preserves (cs : List ReleaseCall) :
    PrefixPreserves ReleaseInv LifetimeEvent.Safe (observe cs) := by
  induction cs with
  | nil => exact PrefixPreserves.pure (fun _ _ hi => hi.safe) ()
  | cons c cs ih => exact PrefixPreserves.bind c.preserves (fun _ => ih)

end ReleaseCall
end Leanux.Proofs.WG.Lifetimes
