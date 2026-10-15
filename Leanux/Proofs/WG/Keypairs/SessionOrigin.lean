import Leanux.Proofs.WG.Keypairs.MaterialOrigin
import Leanux.Proofs.Logged.RxPoll

/-! Session receipts observe allocation and normal front completion. A Some
front receipt is at completed derivation, before zeroing, rotation or index
replacement, and retains the actual peer record and nullable handshake word.
None records only a rejected/refused front. No later residency is asserted. -/
namespace Leanux.Proofs.WG.SessionOrigin
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes MaterialOrigin
set_option pp.structureInstances false

structure Context where
  slot : KeypairId
  state : Nat
  word : Option PeerId
  peer : Peer
  initiator : Bool

/-- Shared source-shaped front. Its last effect is the actual derivation. -/
def frontWith {m : Type → Type} [Monad m]
    (read : PeerId → m Peer) (word : IndexOwner → m (Option PeerId))
    (create : Option PeerId → m (Option KeypairId))
    (initKey : KeypairId → Bool → Nat → m Unit)
    (derive : KeypairId → Bool → List UInt8 → m Unit)
    (step : {α : Type} → M α → m α) (pid : PeerId) : m (Option Context) := do
  let st := (← read pid).handshakeState
  if ← step (sessionStateRejected st) then return none
  let wd ← word (.handshake pid)
  let created ← create wd
  if ← step (branch .sessionNoKeypair created.isNone) then return none
  let some kp := created | step (invariant "unreachable")
  let p ← read pid
  let initiator := st == HANDSHAKE_CONSUMED_RESPONSE
  initKey kp initiator p.remoteIndex
  let direction ← step (branch .sessionInitiator initiator)
  derive kp direction p.chainingKey
  return some ⟨kp, st, wd, p, direction⟩

def initKey (kp : KeypairId) (initiator : Bool) (remoteIndex : Nat) : M Unit := do
  setKeypair kp {(← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex}

def front (pid : PeerId) : M (Option Context) :=
  frontWith getPeer IndexOwner.peerWord keypairCreate initKey deriveKeys (fun a => a) pid

def frontPrefix (pid : PeerId) : MixedM (Option Context) :=
  frontWith getPeerMixed peerWordPrefix keypairCreatePrefix sessionKeypairPrefix deriveKeysPrefix liftPrefix pid

def tailWith {m : Type → Type} [Monad m] (read : PeerId → m Peer)
    (zero : PeerId → m Unit) (rotate : PeerId → KeypairId → m Unit)
    (deref : IndexOwner → m PeerId) (step : {α : Type} → M α → m α)
    (pid : PeerId) (kp : KeypairId) : m Bool := do
  zero pid
  if ← step (branch .sessionAlive !(← read pid).isDead) then
    rotate pid kp
    _ ← deref (.handshake pid)
    if !(← step (indexReplaceHandshake pid kp)) then
      step (unsupported "begin_session: the handshake entry was unhashed")
    return true
  step (unsupported "a dead peer finishing a session")

def tail (pid kp : Nat) : M Bool :=
  tailWith getPeer handshakeZero addNewKeypair IndexOwner.peerDeref (fun a => a) pid kp

def tailPrefix (pid kp : Nat) : MixedM Bool :=
  tailWith getPeerMixed handshakeZeroPrefix addNewKeypairPrefix peerDerefPrefix liftPrefix pid kp

private theorem bind_congr {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (h : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext h)

theorem factor (pid : PeerId) : beginSession pid = (do
    match ← front pid with | none => return false | some c => tail pid c.slot) := by
  unfold front frontWith tail tailWith beginSession initKey sessionStateRejected
  simp only [bind_assoc, pure_bind]
  repeat' first
    | rfl
    | with_reducible apply bind_congr
    | intro_forall
    | (split <;> try simp_all only [bind_assoc, pure_bind, Bool.not_eq_true, Bool.not_eq_false])
    | simp only [bind_assoc, pure_bind]

theorem prefix_factor (pid : PeerId) : beginSessionPrefix pid = (do
    match ← frontPrefix pid with | none => return false | some c => tailPrefix pid c.slot) := by
  unfold frontPrefix frontWith tailPrefix tailWith beginSessionPrefix
  simp only [bind_assoc, pure_bind]
  repeat' first
    | rfl
    | with_reducible apply bind_congr
    | intro_forall
    | (split <;> try simp_all only [bind_assoc, pure_bind, Bool.not_eq_true, Bool.not_eq_false])
    | simp only [bind_assoc, pure_bind]

theorem front_erases (pid : PeerId) : ErasesPrefix (frontPrefix pid) (front pid) := by
  unfold frontPrefix front frontWith initKey
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerWordPrefix_erases _
    | with_reducible exact keypairCreatePrefix_erases _
    | with_reducible exact sessionKeypairPrefix_erases _ _ _
    | with_reducible exact deriveKeysPrefix_erases _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (intro_forall; try dsimp only)
    | split

theorem tail_erases (pid kp : Nat) : ErasesPrefix (tailPrefix pid kp) (tail pid kp) := by
  unfold tailPrefix tail tailWith
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact handshakeZeroPrefix_erases _
    | with_reducible exact addNewKeypairPrefix_erases _ _
    | with_reducible exact peerDerefPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (intro_forall; try dsimp only)
    | split

theorem front_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (frontPrefix pid) := by
  unfold frontPrefix frontWith
  repeat' first
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (peerWordPrefix_spec allocationAmbient (fun _ => True) _)
    | with_reducible exact keypairCreatePrefix_preserves _
    | with_reducible exact AmbientContracts.drop (sessionKeypairPrefix_spec_ambient allocationAmbient (fun _ => True) _ _ _)
    | with_reducible exact AmbientContracts.drop (deriveKeysPrefix_spec_ambient allocationAmbient (fun _ => True) _ _ _)
    | with_reducible exact allocation_kernel _ (sessionStateRejected_sameKernel _)
    | with_reducible exact allocation_kernel _ (Leanux.Proofs.Framing.sameKernel_branch _ _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall; try dsimp only)
    | split

theorem tail_allocation (pid kp : Nat) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (tailPrefix pid kp) := by
  unfold tailPrefix tailWith
  repeat' first
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (handshakeZeroPrefix_spec_ambient allocationAmbient (fun _ => True) _)
    | with_reducible exact addNewKeypairPrefix_preserves_ambient allocationAmbient keypairPutPrefix_allocation _ _
    | with_reducible exact AmbientContracts.drop (peerDerefPrefix_spec allocationAmbient (fun _ => True) _)
    | with_reducible exact indexReplaceHandshake_allocation _ _
    | with_reducible exact allocation_kernel _ (Leanux.Proofs.Framing.sameKernel_branch _ _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.unsupported (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall; try dsimp only)
    | split

inductive Receipt where
  | allocation (word : Option PeerId) (run : RunWitness (Option KeypairId))
  | material (pid : PeerId) (run : RunWitness (Option Context))

def Receipt.Valid : Receipt → Prop
  | .allocation word r => r.Valid (keypairCreate word)
  | .material pid r => r.Valid (front pid)

abbrev Journal := PrefixM (Event Receipt)

def allocate (word : Option PeerId) : Journal (Option KeypairId) :=
  receiptObserved (access (keypairCreatePrefix word)) (Event.receipt ∘ Receipt.allocation word)

def observedFront (pid : PeerId) : Journal (Option Context) :=
  frontWith (fun p => access (getPeerMixed p)) (fun o => access (peerWordPrefix o))
    allocate (fun k b i => access (sessionKeypairPrefix k b i))
    (fun k b ck => access (deriveKeysPrefix k b ck)) liftPrefix pid

def observed (pid : PeerId) : Journal Bool := do
  let result ← receiptObserved (observedFront pid) (Event.receipt ∘ Receipt.material pid)
  match result with
  | none => return false
  | some c => access (tailPrefix pid c.slot)

theorem allocate_erases (word : Option PeerId) : ErasesPrefix (allocate word) (keypairCreate word) :=
  receipt_erases (access_erases (keypairCreatePrefix_erases word)) _

theorem observedFront_erases (pid : PeerId) : ErasesPrefix (observedFront pid) (front pid) := by
  unfold observedFront front frontWith initKey
  repeat' first
    | with_reducible exact access_erases (getPeerMixed_erases _)
    | with_reducible exact access_erases (peerWordPrefix_erases _)
    | with_reducible exact allocate_erases _
    | with_reducible exact access_erases (sessionKeypairPrefix_erases _ _ _)
    | with_reducible exact access_erases (deriveKeysPrefix_erases _ _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (intro_forall; try dsimp only)
    | split

theorem observed_erases (pid : PeerId) : ErasesPrefix (observed pid) (beginSession pid) := by
  rw [factor]
  unfold observed
  apply erasesPrefix_bind (receipt_erases (observedFront_erases pid) _)
  intro result
  cases result with
  | none => exact erasesPrefix_pure _
  | some c => exact access_erases (tail_erases _ _)

theorem allocate_valid (word : Option PeerId) :
    PrefixPreserves (fun h _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (allocate word) :=
  receipt_valid (access_erases (keypairCreatePrefix_erases word))
    (access_valid _ _) _ (fun _ hr => hr)

theorem observedFront_valid (pid : PeerId) :
    PrefixPreserves (fun h _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (observedFront pid) := by
  unfold observedFront frontWith
  repeat' first
    | with_reducible exact access_valid _ _
    | with_reducible exact allocate_valid _
    | with_reducible exact valid_lift Receipt.Valid _
    | with_reducible exact valid_pure Receipt.Valid _
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall; try dsimp only)
    | split

theorem observed_valid (pid : PeerId) :
    PrefixPreserves (fun h _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (observed pid) := by
  unfold observed
  apply PrefixPreserves.bind (receipt_valid (observedFront_erases pid)
    (observedFront_valid pid) (Receipt.material pid) (fun _ hr => hr))
  intro result
  cases result with
  | none => exact valid_pure Receipt.Valid false
  | some c => exact access_valid _ _

theorem allocate_projects (word : Option PeerId) :
    ProjectsUnder AllocationInv life? (allocate word) (keypairCreatePrefix word) :=
  receiptObserved_projectsUnder (fun _ => rfl) (access_projects (keypairCreatePrefix_preserves word))

theorem observedFront_projects (pid : PeerId) :
    ProjectsUnder AllocationInv life? (observedFront pid) (frontPrefix pid) := by
  unfold observedFront frontPrefix frontWith
  repeat' first
    | with_reducible exact allocate_projects _
    | with_reducible exact access_projects (AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _))
    | with_reducible exact access_projects (AmbientContracts.drop (peerWordPrefix_spec allocationAmbient (fun _ => True) _))
    | with_reducible exact access_projects (AmbientContracts.drop (sessionKeypairPrefix_spec_ambient allocationAmbient (fun _ => True) _ _ _))
    | with_reducible exact access_projects (AmbientContracts.drop (deriveKeysPrefix_spec_ambient allocationAmbient (fun _ => True) _ _ _))
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (peerWordPrefix_spec allocationAmbient (fun _ => True) _)
    | with_reducible exact keypairCreatePrefix_preserves _
    | with_reducible exact AmbientContracts.drop (sessionKeypairPrefix_spec_ambient allocationAmbient (fun _ => True) _ _ _)
    | with_reducible exact AmbientContracts.drop (deriveKeysPrefix_spec_ambient allocationAmbient (fun _ => True) _ _ _)
    | with_reducible exact allocation_kernel _ (sessionStateRejected_sameKernel _)
    | with_reducible exact allocation_kernel _ (Leanux.Proofs.Framing.sameKernel_branch _ _)
    | with_reducible apply projectsUnder_bind
    | (intro_forall; try dsimp only)
    | split

theorem observed_projects (pid : PeerId) :
    ProjectsUnder AllocationInv life? (observed pid) (beginSessionPrefix pid) := by
  rw [prefix_factor]
  unfold observed
  apply projectsUnder_bind
    (receiptObserved_projectsUnder (fun _ => rfl) (observedFront_projects pid)) (front_allocation pid)
  intro result
  cases result with
  | none => exact projectsUnder_pure _ _
  | some c => exact access_projects (tail_allocation _ _)

/-- Exact entry-to-allocation-to-peer-read chain, without an unrelated
existential starting World. Allocation refusal has no such successful chain. -/
def Entered (pid : PeerId) (ctx : Context) (w readWorld : World) : Prop :=
  ∃ initial a b c d e,
    (getPeer pid).run w = .ok (initial, a) ∧ ctx.state = initial.handshakeState ∧
    (sessionStateRejected initial.handshakeState).run a = .ok (false, b) ∧
    (IndexOwner.peerWord (.handshake pid)).run b = .ok (ctx.word, c) ∧
    (keypairCreate ctx.word).run c = .ok (some ctx.slot, d) ∧
    (branch .sessionNoKeypair (Option.isNone (some ctx.slot))).run d = .ok (false, e) ∧
    (getPeer pid).run e = .ok (ctx.peer, readWorld)

/-- A Some front receipt identifies the actual post-allocation peer read,
initializer and derivation, with their consecutive Worlds. The prefix run in
the receipt also covers state rejection, the handshake word and allocation. -/
theorem front_material (pid : PeerId) (ctx : Context) (w v : World)
    (hr : (front pid).run w = .ok (some ctx, v)) :
    ∃ readWorld initWorld deriveWorld,
      Entered pid ctx w readWorld ∧
      (getPeer pid).run readWorld = .ok (ctx.peer, readWorld) ∧
      (initKey ctx.slot (ctx.state == HANDSHAKE_CONSUMED_RESPONSE) ctx.peer.remoteIndex).run readWorld = .ok ((), initWorld) ∧
      (branch .sessionInitiator (ctx.state == HANDSHAKE_CONSUMED_RESPONSE)).run initWorld = .ok (ctx.initiator, deriveWorld) ∧
      (deriveKeys ctx.slot ctx.initiator ctx.peer.chainingKey).run deriveWorld = .ok ((), v) ∧
      Derivation ctx.slot ctx.initiator ctx.peer.chainingKey deriveWorld v := by
  unfold front frontWith at hr
  rw [bind_ok] at hr
  obtain ⟨initial, a, hread, hr⟩ := hr
  rw [bind_ok] at hr
  obtain ⟨rejected, b, hrej, hr⟩ := hr
  cases rejected with
  | true => simp at hr
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr
    simp only [bind_ok] at hr
    obtain ⟨word, c, hw, created, d, hc, missing, e, hm, hr⟩ := hr
    cases missing with
    | true => simp at hr
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hr
      cases created with
      | none => simp [invariant] at hr
      | some kp =>
        simp only [bind_ok] at hr
        obtain ⟨peer, f, hp, unit, g, hi, direction, j, hb, unit', k, hd, he⟩ := hr
        cases unit; cases unit'
        have hf : f = e := by
          cases dev : e.k.wg with
          | none => simp [getPeer, getDev, getK, dev, invariant] at hp
          | some device =>
            cases found : device.peers[pid]? with
            | none => simp [getPeer, getDev, getK, dev, found, invariant] at hp
            | some actual =>
              have eqs : actual = peer ∧ e = f := by simpa [getPeer, getDev, getK, dev, found] using hp
              exact eqs.2.symm
        subst f
        simp only [StateT.run_pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨e, g, j, ⟨initial, a, b, c, d, e, hread, rfl, hrej, hw, hc, hm, hp⟩, hp, hi, hb, hd, deriveKeys_execution _ _ _ _ _ hd⟩

end Leanux.Proofs.WG.SessionOrigin
