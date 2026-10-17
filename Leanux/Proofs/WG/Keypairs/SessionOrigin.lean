import Lean
import Leanux.Proofs.WG.Origins.ReceiptTypes
import Leanux.Proofs.WG.Keypairs.MaterialOrigin


/-! Session receipts observe allocation and normal front completion. A Some
front receipt is at completed derivation, before zeroing, rotation or index
replacement, and retains the actual peer record and nullable handshake word.
None records only a rejected/refused front. No later residency is asserted. -/
namespace Leanux.Proofs.WG.SessionOrigin
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes MaterialOrigin
set_option pp.structureInstances false

-- Introduce only explicit callback binders; keep execution contracts opaque.
elab "session_origin_intro_forall" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isForall do
    Lean.throwError "expected an explicit function argument"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro a))

/-- Shared source-shaped front. Its last effect is the actual derivation. -/
def frontWith {m : Type → Type} [Monad m]
    (read : PeerId → m Peer) (word : IndexOwner → m (Option PeerId))
    (create : Option PeerId → m (Option KeypairId))
    (initKey : KeypairId → Bool → Nat → m Unit)
    (derive : KeypairId → Bool → List UInt8 → m Unit)
    (step : {α : Type} → WG.M α → m α) (pid : PeerId) : m (Option Context) := do
  let st := (← read pid).handshakeState
  if ← step (MonadLift.monadLift (sessionStateRejected st) : WG.M Bool) then return none
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

def initKey (kp : KeypairId) (initiator : Bool) (remoteIndex : Nat) : WG.M Unit := do
  setKeypair kp {(← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex}

def front (pid : PeerId) : WG.M (Option Context) :=
  frontWith getPeer IndexOwner.peerWord keypairCreate initKey deriveKeys (fun a => a) pid

def frontPrefix (pid : PeerId) : MixedM (Option Context) :=
  frontWith getPeerMixed peerWordPrefix keypairCreatePrefix sessionKeypairPrefix deriveKeysPrefix liftWGPrefix pid

def tailWith {m : Type → Type} [Monad m] (read : PeerId → m Peer)
    (zero : PeerId → m Unit) (rotate : PeerId → KeypairId → m Unit)
    (deref : IndexOwner → m PeerId) (step : {α : Type} → WG.M α → m α)
    (pid : PeerId) (kp : KeypairId) : m Bool := do
  zero pid
  if ← step (branch .sessionAlive !(← read pid).isDead) then
    rotate pid kp
    _ ← deref (.handshake pid)
    if !(← step (liftIndex (indexReplaceHandshake pid kp))) then
      step (unsupported "begin_session: the handshake entry was unhashed")
    return true
  step (unsupported "a dead peer finishing a session")

def tail (pid kp : Nat) : WG.M Bool :=
  tailWith getPeer handshakeZero addNewKeypair IndexOwner.peerDeref (fun a => a) pid kp

def tailPrefix (pid kp : Nat) : MixedM Bool :=
  tailWith getPeerMixed handshakeZeroPrefix addNewKeypairPrefix peerDerefPrefix liftWGPrefix pid kp

private theorem bind_congr {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (h : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext h)

theorem factor (pid : PeerId) : beginSession pid = (do
    match ← front pid with | none => return false | some c => tail pid c.slot) := by
  have reject_eq (st : Nat) :
      (MonadLift.monadLift (sessionStateRejected st) : WG.M Bool) =
        WG.andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
          (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE)) := by
    change (monadLift (sessionStateRejected st) : WG.M Bool) = _
    simp only [sessionStateRejected, WG.andM, branch, monadLift_bind]
    congr 1
    funext first
    cases first <;> simp only [Bool.false_eq_true, ↓reduceIte, monadLift_pure]
  unfold front frontWith tail tailWith beginSession initKey
  simp only [← reject_eq, bind_assoc]
  repeat' first
    | rfl
    | with_reducible apply bind_congr
    | session_origin_intro_forall
    | (split <;> try simp_all only [bind_assoc, pure_bind, Bool.not_eq_true])
    | simp only [bind_assoc, pure_bind]

theorem prefix_factor (pid : PeerId) : beginSessionPrefix pid = (do
    match ← frontPrefix pid with | none => return false | some c => tailPrefix pid c.slot) := by
  unfold frontPrefix frontWith tailPrefix tailWith beginSessionPrefix
  simp only [bind_assoc]
  repeat' first
    | rfl
    | with_reducible apply bind_congr
    | session_origin_intro_forall
    | (split <;> try simp_all only [bind_assoc, pure_bind, Bool.not_eq_true])
    | simp only [bind_assoc, pure_bind]

theorem front_erases (pid : PeerId) : ErasesStatePrefix (frontPrefix pid) (front pid) := by
  unfold frontPrefix front frontWith initKey
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerWordPrefix_erases _
    | with_reducible exact keypairCreatePrefix_erases _
    | with_reducible exact sessionKeypairPrefix_erases _ _ _
    | with_reducible exact deriveKeysPrefix_erases _ _ _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem tail_erases (pid kp : Nat) : ErasesStatePrefix (tailPrefix pid kp) (tail pid kp) := by
  unfold tailPrefix tail tailWith
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact handshakeZeroPrefix_erases _
    | with_reducible exact addNewKeypairPrefix_erases _ _
    | with_reducible exact peerDerefPrefix_erases _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem front_allocation (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (frontPrefix pid) := by
  unfold frontPrefix frontWith
  apply StatePrefixEnsures.bind (AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) pid))
  intro before
  apply StatePrefixEnsures.bind (AmbientContracts.drop (allocationAmbient.store (fun _ => True) _
    (fun initial => hoare_liftAmbient (sessionStateRejected before.handshakeState)
      (fun w => wgStoreView w = initial))))
  intro rejected
  split
  · exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
  · apply StatePrefixEnsures.bind (AmbientContracts.drop
      (peerWordPrefix_spec allocationAmbient (fun _ => True) (.handshake pid)))
    intro word
    apply StatePrefixEnsures.bind (keypairCreatePrefix_preserves word)
    intro created
    apply StatePrefixEnsures.bind (AmbientContracts.drop
      (allocationAmbient.branch (fun _ => True) .sessionNoKeypair created.isNone))
    intro missing
    split
    · exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
    · cases created with
      | none => exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
      | some kp =>
        apply StatePrefixEnsures.bind (AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) pid))
        intro peer
        apply StatePrefixEnsures.bind (AmbientContracts.drop
          (sessionKeypairPrefix_spec_ambient allocationAmbient (fun _ => True) kp
            (before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) peer.remoteIndex))
        intro _
        apply StatePrefixEnsures.bind (AmbientContracts.drop
          (allocationAmbient.branch (fun _ => True) .sessionInitiator
            (before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE)))
        intro direction
        apply StatePrefixEnsures.bind (AmbientContracts.drop
          (deriveKeysPrefix_spec_ambient allocationAmbient (fun _ => True) kp direction peer.chainingKey))
        intro _
        exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)

theorem tail_allocation (pid kp : Nat) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (tailPrefix pid kp) := by
  unfold tailPrefix tailWith
  repeat' first
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (handshakeZeroPrefix_spec_ambient allocationAmbient (fun _ => True) _)
    | with_reducible exact addNewKeypairPrefix_preserves_ambient allocationAmbient keypairPutPrefix_allocation _ _
    | with_reducible exact AmbientContracts.drop (peerDerefPrefix_spec allocationAmbient (fun _ => True) _)
    | with_reducible exact indexReplaceHandshake_allocation _ _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.unsupported (fun _ => True) _)
    | exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | split


/-- Focus the journal of a local observer, retaining its actual state result. -/
private def accessState {Outer Inner : Type} (a : StatePrefixT LifetimeEvent Outer Inner α) :
    StatePrefixT (Event R) Outer Inner α := focusStatePrefix Event.life life? a

private theorem accessState_erases {Outer Inner : Type}
    {a : StatePrefixT LifetimeEvent Outer Inner α}
    {original : StateT Outer (StateT Inner (Except Stop)) α}
    (ha : ErasesStatePrefix a original) :
    ErasesStatePrefix (accessState (R := R) a) original :=
  focusStatePrefix_erases _ _ ha

private theorem accessState_valid {Outer Inner : Type}
    (a : StatePrefixT LifetimeEvent Outer Inner α) (valid : R → Prop) :
    StatePrefixPreserves (fun h _ _ => Valid valid h) (Valid valid) (accessState a) :=
  fun s => MaterialOrigin.access_valid (a.run s) valid

private theorem accessState_projects {Outer Inner : Type}
    {I : List LifetimeEvent → Outer → Inner → Prop}
    {a : StatePrefixT LifetimeEvent Outer Inner α}
    (ha : StatePrefixPreserves I LifetimeEvent.Safe a) :
    StateProjectsUnder I life? (accessState (R := R) a) a :=
  stateProjectsUnder_focus Event.life life? (fun _ => rfl) ha

private theorem validState_lift {Outer Inner : Type}
    (valid : R → Prop) (a : StateT Outer (StateT Inner (Except Stop)) α) :
    StatePrefixPreserves (fun h _ _ => Valid valid h) (Valid valid) (liftStatePrefix a) :=
  fun s => MaterialOrigin.valid_lift valid (a.run s)

private theorem validState_pure {Outer Inner : Type} (valid : R → Prop) (x : α) :
    StatePrefixPreserves (fun h (_ : Outer) (_ : Inner) => Valid valid h) (Valid valid) (pure x) :=
  fun s => MaterialOrigin.valid_pure valid (x, s)

private theorem receiptState_valid {R α : Type} {a : WGPrefix (Event R) α}
    {original : WG.M α} {valid : R → Prop} (ha : ErasesStatePrefix a original)
    (hp : StatePrefixPreserves (fun h _ _ => Valid valid h) (Valid valid) a)
    (f : WGRunWitness α → R) (hf : ∀ r, r.Valid original → valid (f r)) :
    StatePrefixPreserves (fun h _ _ => Valid valid h) (Valid valid)
      (receiptWGObserved a (Event.receipt ∘ f)) := by
  intro w ambient h hi
  obtain ⟨suffix, hs, hv, _⟩ := hp w ambient h hi
  have hc := runWGPrefix_receiptWGObserved a (Event.receipt ∘ f) w ambient h
  simp only [runWGPrefix, runStatePrefix] at hc
  rw [hc]
  cases hr : runPrefix (a.run w) ambient h with
  | mk out t =>
    simp only [hr] at hs hv
    cases out with
    | error e => exact ⟨suffix, hs, hv, trivial⟩
    | ok out =>
      rcases out with ⟨⟨x, v⟩, ambient'⟩
      have hv' : Valid valid (t ++ [Event.receipt (f ⟨x, w, v, ambient, ambient'⟩)]) := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hv e he
        · simp only [List.mem_singleton] at he
          subst e
          exact hf _ ((ha w ambient h).symm.trans (congrArg Prod.fst hr))
      exact ⟨suffix ++ [Event.receipt (f ⟨x, w, v, ambient, ambient'⟩)],
        by simp [hs, List.append_assoc], hv', hv'⟩

private theorem receiptState_projects {I : List F → WGWorld → Ambient → Prop}
    {ρ : E → Option F} {a : WGPrefix E α} {b : WGPrefix F α}
    {receipt : WGRunWitness α → E}
    (hr : ∀ r, ρ (receipt r) = none) (ha : StateProjectsUnder I ρ a b) :
    StateProjectsUnder I ρ (receiptWGObserved a receipt) b := by
  intro w ambient h hi
  change runWGPrefix b w ambient (h.filterMap ρ) =
    ((runWGPrefix (receiptWGObserved a receipt) w ambient h).1,
      (runWGPrefix (receiptWGObserved a receipt) w ambient h).2.filterMap ρ)
  rw [show runWGPrefix b w ambient (h.filterMap ρ) =
    ((runWGPrefix a w ambient h).1, (runWGPrefix a w ambient h).2.filterMap ρ) from ha w ambient h hi,
    runWGPrefix_receiptWGObserved]
  cases runWGPrefix a w ambient h with
  | mk out hist => cases out <;> simp [List.filterMap_append, hr]

def Receipt.Valid : Receipt → Prop
  | .allocation word r => r.Valid (keypairCreate word)
  | .material pid r => r.Valid (front pid)

abbrev Journal := WGPrefix (Event Receipt)

def allocate (word : Option PeerId) : Journal (Option KeypairId) :=
  receiptWGObserved (accessState (keypairCreatePrefix word)) (Event.receipt ∘ Receipt.allocation word)

def observedFront (pid : PeerId) : Journal (Option Context) :=
  frontWith (fun p => accessState (getPeerMixed p)) (fun o => accessState (peerWordPrefix o))
    allocate (fun k b i => accessState (sessionKeypairPrefix k b i))
    (fun k b ck => accessState (deriveKeysPrefix k b ck)) liftWGPrefix pid

def observed (pid : PeerId) : Journal Bool := do
  let result ← receiptWGObserved (observedFront pid) (Event.receipt ∘ Receipt.material pid)
  match result with
  | none => return false
  | some c => accessState (tailPrefix pid c.slot)

theorem allocate_erases (word : Option PeerId) : ErasesStatePrefix (allocate word) (keypairCreate word) :=
  receiptWGObserved_erases (accessState_erases (keypairCreatePrefix_erases word)) _

theorem observedFront_erases (pid : PeerId) : ErasesStatePrefix (observedFront pid) (front pid) := by
  unfold observedFront front frontWith initKey
  repeat' first
    | with_reducible exact accessState_erases (getPeerMixed_erases _)
    | with_reducible exact accessState_erases (peerWordPrefix_erases _)
    | with_reducible exact allocate_erases _
    | with_reducible exact accessState_erases (sessionKeypairPrefix_erases _ _ _)
    | with_reducible exact accessState_erases (deriveKeysPrefix_erases _ _ _)
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem observed_erases (pid : PeerId) : ErasesStatePrefix (observed pid) (beginSession pid) := by
  rw [factor]
  unfold observed
  apply erasesStatePrefix_bind (receiptWGObserved_erases (observedFront_erases pid) _)
  intro result
  cases result with
  | none => exact erasesStatePrefix_pure _
  | some c => exact accessState_erases (tail_erases _ _)

theorem allocate_valid (word : Option PeerId) :
    StatePrefixPreserves (fun h _ _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (allocate word) :=
  receiptState_valid (accessState_erases (keypairCreatePrefix_erases word))
    (accessState_valid _ _) _ (fun _ hr => hr)

theorem observedFront_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (observedFront pid) := by
  unfold observedFront frontWith
  repeat' first
    | with_reducible exact accessState_valid _ _
    | with_reducible exact allocate_valid _
    | exact validState_lift Receipt.Valid _
    | exact validState_pure Receipt.Valid _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem observed_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (observed pid) := by
  unfold observed
  apply StatePrefixEnsures.bind (receiptState_valid (observedFront_erases pid)
    (observedFront_valid pid) (Receipt.material pid) (fun _ hr => hr))
  intro result
  cases result with
  | none => exact validState_pure Receipt.Valid false
  | some c => exact accessState_valid _ _

theorem allocate_projects (word : Option PeerId) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) life? (allocate word) (keypairCreatePrefix word) :=
  receiptState_projects (fun _ => rfl) (accessState_projects (keypairCreatePrefix_preserves word))

theorem observedFront_projects (pid : PeerId) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) life? (observedFront pid) (frontPrefix pid) := by
  unfold observedFront frontPrefix frontWith
  apply stateProjectsUnder_bind
    (accessState_projects (AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) pid)))
    (AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) pid))
  intro before
  apply stateProjectsUnder_bind (stateProjectsUnder_lift _ _)
    (AmbientContracts.drop (allocationAmbient.store (fun _ => True) _
      (fun initial => hoare_liftAmbient (sessionStateRejected before.handshakeState)
        (fun w => wgStoreView w = initial))))
  intro rejected
  split
  · exact stateProjectsUnder_pure _ _
  · apply stateProjectsUnder_bind
      (accessState_projects (AmbientContracts.drop
        (peerWordPrefix_spec allocationAmbient (fun _ => True) (.handshake pid))))
      (AmbientContracts.drop (peerWordPrefix_spec allocationAmbient (fun _ => True) (.handshake pid)))
    intro word
    apply stateProjectsUnder_bind (allocate_projects word) (keypairCreatePrefix_preserves word)
    intro created
    apply stateProjectsUnder_bind (stateProjectsUnder_lift _ _)
      (AmbientContracts.drop (allocationAmbient.branch (fun _ => True) .sessionNoKeypair created.isNone))
    intro missing
    split
    · exact stateProjectsUnder_pure _ _
    · cases created with
      | none => exact stateProjectsUnder_lift _ _
      | some kp =>
        apply stateProjectsUnder_bind
          (accessState_projects (AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) pid)))
          (AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) pid))
        intro peer
        apply stateProjectsUnder_bind
          (accessState_projects (AmbientContracts.drop
            (sessionKeypairPrefix_spec_ambient allocationAmbient (fun _ => True) kp
              (before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) peer.remoteIndex)))
          (AmbientContracts.drop
            (sessionKeypairPrefix_spec_ambient allocationAmbient (fun _ => True) kp
              (before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) peer.remoteIndex))
        intro _
        apply stateProjectsUnder_bind (stateProjectsUnder_lift _ _)
          (AmbientContracts.drop (allocationAmbient.branch (fun _ => True) .sessionInitiator
            (before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE)))
        intro direction
        apply stateProjectsUnder_bind
          (accessState_projects (AmbientContracts.drop
            (deriveKeysPrefix_spec_ambient allocationAmbient (fun _ => True) kp direction peer.chainingKey)))
          (AmbientContracts.drop
            (deriveKeysPrefix_spec_ambient allocationAmbient (fun _ => True) kp direction peer.chainingKey))
        intro _
        exact stateProjectsUnder_pure _ _

theorem observed_projects (pid : PeerId) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) life? (observed pid) (beginSessionPrefix pid) := by
  rw [prefix_factor]
  unfold observed
  apply stateProjectsUnder_bind
    (receiptState_projects (fun _ => rfl) (observedFront_projects pid)) (front_allocation pid)
  intro result
  cases result with
  | none => exact stateProjectsUnder_pure _ _
  | some c => exact accessState_projects (tail_allocation _ _)

/-- Exact entry-to-allocation-to-peer-read chain, without an unrelated
existential starting World. Allocation refusal has no such successful chain. -/
def Entered (pid : PeerId) (ctx : Context) (w readWorld : WGWorld)
    (ambient readAmbient : Ambient) : Prop :=
  ∃ initial a aAmbient b bAmbient c cAmbient d dAmbient e eAmbient,
    ((getPeer pid).run w).run ambient = .ok ((initial, a), aAmbient) ∧ ctx.state = initial.handshakeState ∧
    ((MonadLift.monadLift (sessionStateRejected initial.handshakeState) : WG.M Bool).run a).run aAmbient = .ok ((false, b), bAmbient) ∧
    ((IndexOwner.peerWord (.handshake pid)).run b).run bAmbient = .ok ((ctx.word, c), cAmbient) ∧
    ((keypairCreate ctx.word).run c).run cAmbient = .ok ((some ctx.slot, d), dAmbient) ∧
    ((branch .sessionNoKeypair (Option.isNone (some ctx.slot)) : WG.M Bool).run d).run dAmbient = .ok ((false, e), eAmbient) ∧
    ((getPeer pid).run e).run eAmbient = .ok ((ctx.peer, readWorld), readAmbient)

/-- A successful front exposes consecutive native states at its actual cuts. -/
theorem front_material (pid : PeerId) (ctx : Context) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((front pid).run w).run ambient = .ok ((some ctx, v), ambient')) :
    ∃ readWorld initWorld deriveWorld readAmbient initAmbient deriveAmbient,
      Entered pid ctx w readWorld ambient readAmbient ∧
      ((getPeer pid).run readWorld).run readAmbient = .ok ((ctx.peer, readWorld), readAmbient) ∧
      ((initKey ctx.slot (ctx.state == HANDSHAKE_CONSUMED_RESPONSE) ctx.peer.remoteIndex).run readWorld).run readAmbient =
        .ok (((), initWorld), initAmbient) ∧
      ((branch .sessionInitiator (ctx.state == HANDSHAKE_CONSUMED_RESPONSE) : WG.M Bool).run initWorld).run initAmbient =
        .ok ((ctx.initiator, deriveWorld), deriveAmbient) ∧
      ((deriveKeys ctx.slot ctx.initiator ctx.peer.chainingKey).run deriveWorld).run deriveAmbient = .ok (((), v), ambient') ∧
      Derivation ctx.slot ctx.initiator ctx.peer.chainingKey deriveWorld v deriveAmbient ambient' := by
  unfold front frontWith at hr
  rw [bind_ok_ambient] at hr
  obtain ⟨initial, a, aAmbient, hread, hr⟩ := hr
  rw [bind_ok_ambient] at hr
  obtain ⟨rejected, b, bAmbient, hrej, hr⟩ := hr
  cases rejected with
  | true => simp at hr
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr
    simp only [bind_ok_ambient] at hr
    obtain ⟨word, c, cAmbient, hw, created, d, dAmbient, hc, missing, e, eAmbient, hm, hr⟩ := hr
    cases missing with
    | true => simp at hr
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hr
      cases created with
      | none =>
        simp [invariant, AmbientM.invariant] at hr
        cases hr
      | some kp =>
        simp only [bind_ok_ambient] at hr
        obtain ⟨peer, f, fAmbient, hp, firstResult, g, gAmbient, hi, direction, j, jAmbient, hb,
          secondResult, k, kAmbient, hd, he⟩ := hr
        cases firstResult; cases secondResult
        have hg := Peers.getPeer_current pid e f peer eAmbient fAmbient hp
        have hf := hg.1
        have hfAmbient := hg.2.1
        subst f
        subst fAmbient
        simp only [StateT.run_pure] at he
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
        exact ⟨e, g, j, eAmbient, gAmbient, jAmbient,
          ⟨initial, a, aAmbient, b, bAmbient, c, cAmbient, d, dAmbient, e, eAmbient,
            hread, rfl, hrej, hw, hc, hm, hp⟩,
          hp, hi, hb, hd, deriveKeys_execution _ _ _ _ _ _ _ hd⟩

end Leanux.Proofs.WG.SessionOrigin
