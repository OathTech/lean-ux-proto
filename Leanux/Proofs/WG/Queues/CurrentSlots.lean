import Leanux.Proofs.WG.Queues.CurrentKeys

/-! Only the nullable key references in the three peer slots are carried here.
No TX-packet, RX-packet, peer-word or global allocation invariant is assumed. -/
namespace Leanux.Proofs.WG.CurrentSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
open Lifetimes Affiliation

def SlotInv (s : Affiliation.State) : Prop :=
  ∀ pid p kid, s.peers pid = some p →
    (p.2.2.1 = some kid ∨ p.2.2.2.1 = some kid ∨ p.2.2.2.2 = some kid) → s.keyRef pid kid

def Inv (w : WGWorld) : Prop := ∀ s, Affiliation.view w = some s → SlotInv s

theorem of_affiliation (hi : Affiliation.Inv w) : Inv w := fun s hs => (hi s hs).slots

theorem current (hi : Inv w) : CurrentKeys.Inv w := by
  constructor
  · intro pid d p kid hd hp current other key ho hk
    have eq : other = d := Option.some.inj (ho.symm.trans hd)
    subst other
    have ref := hi (Affiliation.state d) (by simp [Affiliation.view,hd]) pid
      (Affiliation.peerCell p) kid (by simp [Affiliation.state,hp]) (Or.inl current)
    exact ref.2 key.internalId key.peer (by simp [Affiliation.state,Affiliation.keyCell,hk])
  · intro d pid p kid hd hp current
    exact (hi (Affiliation.state d) (by simp [Affiliation.view,hd]) pid
      (Affiliation.peerCell p) kid (by simp [Affiliation.state,hp]) (Or.inl current)).1

theorem initial (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) : Inv w :=
  of_affiliation (Affiliation.initial net bare w hw)

theorem keyRef_erase {s : Affiliation.State} (h : s.keyRef pid kid) (removed : KeypairId) :
    (s.eraseKey removed).keyRef pid kid := by
  refine ⟨h.1, ?_⟩
  intro stamp word hk
  by_cases same : kid = removed
  · simp [State.eraseKey,same] at hk
  · exact h.2 _ _ (by simpa [State.eraseKey,same] using hk)

theorem erase (hi : SlotInv s) (removed : KeypairId) : SlotInv (s.eraseKey removed) := by
  intro pid p kid hp hs
  exact keyRef_erase (hi pid p kid hp hs) removed

theorem setSlots (hi : SlotInv s) (pid : PeerId)
    (current previous next : Option KeypairId)
    (refs : ∀ kid, current = some kid ∨ previous = some kid ∨ next = some kid → s.keyRef pid kid) :
    SlotInv (s.setSlots pid current previous next) := by
  intro q p kid hp hs
  by_cases same : q = pid
  · subst q
    simp only [State.setSlots,ite_true] at hp
    obtain ⟨old,ho,rfl⟩ := Option.map_eq_some_iff.mp hp
    exact refs kid hs
  · exact hi q p kid (by simpa [State.setSlots,same] using hp) hs

def References (pid : PeerId) (keys : List KeypairId) (v : Option Affiliation.State) : Prop :=
  ∀ s, v = some s → SlotInv s ∧ ∀ kid ∈ keys, s.keyRef pid kid

theorem References.erase (h : References pid keys (some s)) (kid : KeypairId) :
    References pid keys (some (s.eraseKey kid)) := by
  intro t ht
  cases ht
  exact ⟨CurrentSlots.erase (h s rfl).1 kid,fun k hk => keyRef_erase ((h s rfl).2 k hk) kid⟩

theorem modifyPeer_slots (pid : PeerId) (keys : List KeypairId) (f : Peer → Peer)
    (stamp : ∀ p, (f p).internalId = p.internalId)
    (word : ∀ p, (f p).handshakeEntryPeer = p.handshakeEntryPeer)
    (slots : ∀ p kid, (f p).keypairCurrent = some kid ∨ (f p).keypairPrevious = some kid ∨ (f p).keypairNext = some kid →
      p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid ∨ kid ∈ keys) :
    ⦃fun w => ⌜References pid keys (view w)⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f
    ⦃⇓? _ w => ⌜References pid keys (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  change ((do let p ← getPeer pid; setPeer pid (f p)).run w).run ambient = .ok ((x, v), ambient') at hr
  cases hd : w.dev with
  | none => simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hr; cases hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr; cases hr
    | some p =>
      simp [getPeer, getDev, hd, hp, setPeer, modifyDev] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hs : state {d with peers := d.peers.insert pid (f p)} =
          (state d).setSlots pid (f p).keypairCurrent (f p).keypairPrevious (f p).keypairNext := by
        unfold state State.setSlots
        congr 1
        funext q
        by_cases he : pid = q
        · subst q; simp [hp, peerCell, stamp, word]
        · simp [Std.TreeMap.getElem?_insert, he, Ne.symm he]
      have orig := hi (state d) (by simp [view, hd])
      intro s hview
      simp only [view, Option.map_some, hs, Option.some.injEq] at hview
      subst s
      refine ⟨setSlots orig.1 pid _ _ _ ?_, orig.2⟩
      intro kid hh
      rcases slots p kid hh with hc | hp' | hn | hk
      · exact orig.1 pid (peerCell p) kid (by simp [state, hp]) (Or.inl hc)
      · exact orig.1 pid (peerCell p) kid (by simp [state, hp]) (Or.inr (Or.inl hp'))
      · exact orig.1 pid (peerCell p) kid (by simp [state, hp]) (Or.inr (Or.inr hn))
      · exact orig.2 kid hk

theorem getPeer_references (pid : PeerId) (keys : List KeypairId) :
    ⦃fun w => ⌜References pid keys (view w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜References pid (keys ++ peerKeys p) (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hi hr
  have hg := (hoare_iff_run_ambient _ _ _).mp (getPeer_spec (References pid keys) pid)
    w ambient p v ambient' hi hr
  intro s hs
  refine ⟨(hg.1 s hs).1, ?_⟩
  intro kid hk
  rcases List.mem_append.mp hk with hk | hk
  · exact (hg.1 s hs).2 kid hk
  · have hp : s.peers pid = some (peerCell p) := by
      cases hd : v.dev with
      | none => simp [view, hd] at hs
      | some d =>
        simp only [view, hd, Option.map_some, Option.some.injEq] at hs
        subst s
        simpa [peerAt, hd, state] using hg.2
    apply (hg.1 s hs).1 pid (peerCell p) kid hp
    simpa [peerKeys, peerCell, List.mem_append, Option.mem_toList] using hk

theorem rotateSource_preserves (pid kid : Nat) (p : Peer) :
    ⦃fun w => ⌜References pid ([kid] ++ peerKeys p) (view w)⌝⦄ rotateSource pid kid p
    ⦃⇓? _ w => ⌜References pid ([kid] ++ peerKeys p) (view w)⌝⦄ := by
  let keys := [kid] ++ peerKeys p
  let P := fun w => References pid keys (view w)
  have hkey : Preserves P (getKeypair kid) :=
    hoare_consequence (getKeypair_spec (References pid keys) kid)
      (fun _ h => h) (fun _ _ h => h.1)
  have hp := fun old => keypairPut_affiliation (References pid keys)
    (fun _ _ h => h.erase _) old true
  have h1 := modifyPeer_slots pid keys (fun q => {q with keypairNext := none, keypairPrevious := p.keypairNext})
    (fun _ => rfl) (fun _ => rfl) (by intro q k hh; simp_all [keys, peerKeys]; grind)
  have h2 := modifyPeer_slots pid keys (fun q => {q with keypairPrevious := p.keypairCurrent})
    (fun _ => rfl) (fun _ => rfl) (by intro q k hh; simp_all [keys, peerKeys]; grind)
  have h3 := modifyPeer_slots pid keys (fun q => {q with keypairCurrent := some kid})
    (fun _ => rfl) (fun _ => rfl) (by intro q k hh; simp_all [keys, peerKeys]; grind)
  have h4 := modifyPeer_slots pid keys (fun q => {q with keypairNext := some kid})
    (fun _ => rfl) (fun _ => rfl) (by intro q k hh; simp_all [keys, peerKeys]; grind)
  have h5 := modifyPeer_slots pid keys (fun q => {q with keypairPrevious := none})
    (fun _ => rfl) (fun _ => rfl) (by intro q k hh; simp_all [keys, peerKeys]; grind)
  change Preserves P (rotateSource pid kid p)
  unfold rotateSource
  apply preserves_bind hkey
  intro key
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .addKeypairInitiator key.iAmTheInitiator) P)
  intro initiator
  cases initiator with
  | false =>
    exact preserves_bind h4 (fun _ =>
      preserves_bind (hp p.keypairNext) (fun _ =>
        preserves_bind h5 (fun _ => hp p.keypairPrevious)))
  | true =>
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .addKeypairHasNext p.keypairNext.isSome) P)
    intro hasNext
    cases hasNext with
    | false => exact preserves_bind h2 (fun _ => preserves_bind (hp p.keypairPrevious) (fun _ => h3))
    | true => exact preserves_bind h1 (fun _ =>
        preserves_bind (hp p.keypairCurrent) (fun _ =>
          preserves_bind (hp p.keypairPrevious) (fun _ => h3)))

/-- Actual original rotation under nullable compatibility of the incoming key.
Old slots may alias or already name absent keys; original getters may Stop. -/
theorem addNewKeypair_preserves (pid : PeerId) (kid : KeypairId) :
    ⦃fun w => ⌜References pid [kid] (view w)⌝⦄ addNewKeypair pid kid
    ⦃⇓? _ w => ⌜Inv w⌝⦄ := by
  rw [rotateSource_eq]
  apply hoare_bind _ _ (getPeer_references pid [kid])
  intro p
  exact hoare_consequence (rotateSource_preserves pid kid p)
    (fun _ h => h) (fun _ _ h s hs => (h s hs).1)


theorem allocate (hi : SlotInv s) (stamp : Nat) (word : Option PeerId) :
    SlotInv (s.allocate stamp word) := by
  intro pid p kid hp hs
  have old := hi pid p kid hp hs
  refine ⟨Nat.lt_trans old.1 (Nat.lt_succ_self _), ?_⟩
  intro st wd hk
  exact old.2 st wd (by simpa [State.allocate,Nat.ne_of_lt old.1] using hk)

theorem keypairCreateCore_for_peer (pid : PeerId) (word : Option PeerId) :
    Hoare (keypairCreateCore word) (fun w => Inv w ∧ Compatible word pid)
      (fun kid w => References pid [kid] (view w)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a kid v b hi hr
  rw [keypairCreateCore_run] at hr
  cases hd : w.dev with
  | none => simp [hd] at hr
  | some d =>
    simp only [hd,Except.ok.injEq,Prod.mk.injEq] at hr
    rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩
    have old := hi.1 (state d) (by simp [view,hd])
    have next : view (keyAllocationWorld w d word) =
        some ((state d).allocate (w.keypairCounter + 1) word) := by
      simp [view,keyAllocationWorld,allocation_state]
    intro out ho
    rw [next] at ho
    cases ho
    refine ⟨allocate old _ word, ?_⟩
    intro k hk
    have eq : k = d.nextKeypairId := by simpa using hk
    subst k
    refine ⟨Nat.lt_succ_self _, ?_⟩
    intro stamp value stored
    have wordEq : word = value := by
      have fields : (w.keypairCounter + 1, word) = (stamp, value) := by
        simpa only [State.allocate,state,ite_true,Option.some.injEq] using stored
      exact congrArg Prod.snd fields
    exact wordEq ▸ hi.2

theorem keypairCreate_for_peer (pid : PeerId) (word : Option PeerId) :
    Hoare (keypairCreate word) (fun w => Inv w ∧ Compatible word pid)
      (fun result w => Inv w ∧ ∀ kid, result = some kid → References pid [kid] (view w)) := by
  rw [keypairCreate_factor]
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.hiddenAlloc .kzallocKeypair)
    (fun w => Inv w ∧ Compatible word pid))
  intro ok
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .keypairCreateNoMem (!ok))
    (fun w => Inv w ∧ Compatible word pid))
  intro refused
  cases refused with
  | true =>
    apply hoare_consequence (hoare_pure none (fun w => Inv w ∧ Compatible word pid))
    · exact fun _ h => h
    · intro x w h
      rcases h with ⟨rfl,hi,_⟩
      exact ⟨hi,by simp⟩
  | false =>
    apply hoare_bind _ _ (keypairCreateCore_for_peer pid word)
    intro kid
    apply hoare_consequence (hoare_pure (some kid) (fun w => References pid [kid] (view w)))
    · exact fun _ h => h
    · intro x w h
      rcases h with ⟨rfl,hi⟩
      exact ⟨fun s hs => (hi s hs).1,fun k hk => by cases hk; exact hi⟩

private theorem read (pid : PeerId) (P : WGWorld → Prop) : Preserves P (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi hr
  obtain ⟨rfl,_,_,_,_⟩ := Origins.getPeer_return _ _ _ _ _ _ hr
  exact hi

theorem handshake_input (pid : PeerId) :
    Hoare (IndexOwner.peerWord (.handshake pid))
      (fun w => Inv w ∧ ConfiguredIdentity.Inv w)
      (fun word w => Inv w ∧ Compatible word pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a word v b hi hr
  unfold IndexOwner.peerWord at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,u,middle,hg,hret⟩ := hr
  obtain ⟨rfl,rfl,d,hd,hp⟩ := Origins.getPeer_return _ _ _ _ _ _ hg
  cases hret
  exact ⟨hi.1,(hi.2 (ConfiguredIdentity.state d)
    (by simp [ConfiguredIdentity.view,hd])).self pid (ConfiguredIdentity.cell p)
      (by simp [ConfiguredIdentity.state,hp])⟩

theorem sessionTail_preserves (pid st kp : Nat) :
    ⦃fun w => ⌜References pid [kp] (view w)⌝⦄ sessionTail pid st kp
    ⦃⇓? _ w => ⌜Inv w⌝⦄ := by
  let R := fun w => References pid [kp] (view w)
  have peer : Preserves R (getPeer pid) :=
    hoare_consequence (getPeer_spec (References pid [kp]) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  have stopped {α : Type} (why : String) (P : WGWorld → Prop) (Q : α → WGWorld → Prop) :
      Hoare (unsupported why : WG.M α) P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v a' h hr
    simp [unsupported, AmbientM.unsupported] at hr
    cases hr
  have hi : Preserves Inv (monadLift (indexReplaceHandshake pid kp) : WG.M Bool) := by
    apply hoare_liftIndex
    intro g d table h hdev
    simpa only [Inv, view, hdev, Option.map_some, state] using h
  have finish : Hoare (do
      handshakeZero pid
      if ← branch .sessionAlive !(← getPeer pid).isDead then
        addNewKeypair pid kp
        _ ← IndexOwner.peerDeref (.handshake pid)
        if !(← indexReplaceHandshake pid kp) then unsupported "begin_session: the handshake entry was unhashed"
        return true
      unsupported "a dead peer finishing a session") R (fun _ => Inv) := by
    apply hoare_bind _ _ ((handshakeZero_view pid).wp (References pid [kp]))
    intro _
    apply hoare_bind _ _ peer
    intro p
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .sessionAlive (!p.isDead)) R)
    intro alive
    cases alive with
    | false => exact stopped _ _ _
    | true =>
      apply hoare_bind _ _ (addNewKeypair_preserves pid kp)
      intro _
      apply preserves_bind (indexOwner_peerDeref_preserves (.handshake pid) Inv)
      intro _
      apply preserves_bind hi
      intro replaced
      cases replaced with
      | false => exact stopped _ _ _
      | true => exact preserves_pure true
  unfold sessionTail
  apply hoare_bind _ _ peer
  intro p
  apply hoare_bind _ _ (getKeypair_spec (References pid [kp]) kp)
  intro key
  apply hoare_bind _ _ (setKeypair_spec (References pid [kp]) kp
    {key with iAmTheInitiator := st == HANDSHAKE_CONSUMED_RESPONSE, remoteIndex := p.remoteIndex})
  intro _
  apply hoare_bind _ _ (hoare_liftAmbient
    (AmbientM.branch .sessionInitiator (st == HANDSHAKE_CONSUMED_RESPONSE)) R)
  intro initiator
  cases initiator with
  | false =>
    exact hoare_bind _ _ ((deriveKeys_view kp false p.chainingKey).wp (References pid [kp]))
      (fun _ => finish)
  | true =>
    exact hoare_bind _ _ ((deriveKeys_view kp true p.chainingKey).wp (References pid [kp]))
      (fun _ => finish)

/-- Complete native session rotation needs only slot references and the actual
configured handshake self word. Allocation and hidden-record failure remain
partial; every normal false or true result retains the same weak slot invariant. -/
theorem beginSession_preserves (pid : PeerId) :
    Hoare (beginSession pid) (fun w => Inv w ∧ ConfiguredIdentity.Inv w) (fun _ => Inv) := by
  let P := fun w => Inv w ∧ ConfiguredIdentity.Inv w
  have ambient {α : Type} (a : AmbientM α) (P : WGWorld → Prop) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have condition (st : Nat) : Preserves P
      (WG.andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
        (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE))) := by
    unfold WG.andM
    apply preserves_bind (ambient
      (AmbientM.branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE)) P)
    intro b
    cases b with
    | false => exact preserves_pure false
    | true =>
      exact ambient
        (AmbientM.branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE)) P
  rw [sessionTail_eq]
  apply hoare_bind _ _ (read pid P)
  intro peer
  apply hoare_bind _ _ (condition peer.handshakeState)
  intro skip
  cases skip with
  | true =>
    simp only [ite_true]
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi hr
    cases hr
    exact hi.1
  | false =>
    apply hoare_bind _ _ (handshake_input pid)
    intro word
    apply hoare_bind _ _ (keypairCreate_for_peer pid word)
    intro created
    apply hoare_bind _ _ (ambient (AmbientM.branch .sessionNoKeypair created.isNone)
      (fun w => Inv w ∧ ∀ kid, created = some kid → References pid [kid] (view w)))
    intro noKey
    cases noKey with
    | true =>
      simp only [ite_true]
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b hi hr
      cases hr
      exact hi.1
    | false =>
      cases created with
      | none =>
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a x v b hi hr
        simp [invariant,AmbientM.invariant] at hr
        cases hr
      | some kp =>
        exact hoare_consequence (sessionTail_preserves pid peer.handshakeState kp)
          (fun _ h => h.2 kp rfl) (fun _ _ h => h)


theorem keypairCreate_preserves (word : Option PeerId) : Preserves Inv (keypairCreate word) := by
  apply hoare_consequence (keypairCreate_for_peer (word.getD 0) word)
  · intro w hi
    exact ⟨hi,by cases word <;> simp [Compatible]⟩
  · exact fun _ _ h => h.1

theorem keypairPut_preserves (kp : Option KeypairId) (now : Bool) :
    Preserves Inv (keypairPut kp now) :=
  keypairPut_affiliation (fun v => ∀ s, v = some s → SlotInv s)
    (by intro s kid hi t ht; cases ht; exact CurrentSlots.erase (hi s rfl) kid) kp now

private theorem modify_subset (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p, (f p).internalId = p.internalId)
    (word : ∀ p, (f p).handshakeEntryPeer = p.handshakeEntryPeer)
    (slots : ∀ p kid, (f p).keypairCurrent = some kid ∨
      (f p).keypairPrevious = some kid ∨ (f p).keypairNext = some kid →
      p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid) :
    Preserves Inv ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by
  apply hoare_consequence (modifyPeer_slots pid [] f stamp word (by
    intro p kid h
    rcases slots p kid h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))))
  · intro w hi s hs
    exact ⟨hi s hs,by simp⟩
  · exact fun _ w h s hs => (h s hs).1

theorem keypairsClear_preserves (pid : PeerId) : Preserves Inv (keypairsClear pid) := by
  unfold keypairsClear
  apply preserves_bind (read pid Inv)
  intro p
  apply preserves_bind (modify_subset pid (fun p => {p with keypairNext := none})
    (fun _ => rfl) (fun _ => rfl) (by
      intro p kid h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · cases h))
  intro _
  apply preserves_bind (keypairPut_preserves p.keypairNext true)
  intro _
  apply preserves_bind (read pid Inv)
  intro p
  apply preserves_bind (modify_subset pid (fun p => {p with keypairPrevious := none})
    (fun _ => rfl) (fun _ => rfl) (by
      intro p kid h
      rcases h with h | h | h
      · exact Or.inl h
      · cases h
      · exact Or.inr (Or.inr h)))
  intro _
  apply preserves_bind (keypairPut_preserves p.keypairPrevious true)
  intro _
  apply preserves_bind (read pid Inv)
  intro p
  apply preserves_bind (modify_subset pid (fun p => {p with keypairCurrent := none})
    (fun _ => rfl) (fun _ => rfl) (by
      intro p kid h
      rcases h with h | h | h
      · cases h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)))
  intro _
  exact keypairPut_preserves p.keypairCurrent true

/-- This observation adapter retains arbitrary outer state/monad and hence
actual product callbacks; only the stated slot observation must be preserved. -/
theorem view_preserves {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => Affiliation.view (project w)) a) :
    Preserves (fun w => Inv (project w)) a :=
  ha.wp (fun v => ∀ s, v = some s → SlotInv s)

theorem handshakeClear_preserves (pid : PeerId) : Preserves Inv (handshakeClear pid) :=
  view_preserves (project := id) (Affiliation.handshakeClear_view pid)

theorem expireCurrentPeerKeypairs_preserves (pid : PeerId) :
    Preserves Inv (expireCurrentPeerKeypairs pid) :=
  view_preserves (project := id) (Affiliation.expireCurrentPeerKeypairs_view pid)


private theorem received_references (pid : PeerId) (kid : KeypairId) :
    Preserves (fun w => References pid [kid] (view w)) (receivedWithKeypair pid kid) := by
  let P := fun w => References pid [kid] (view w)
  have readPeer : Preserves P (getPeer pid) := read pid P
  have ambient (decision : Decision) (value : Bool) : Preserves P (branch decision value) :=
    hoare_liftAmbient (AmbientM.branch decision value) P
  have put (old : Option KeypairId) : Preserves P (keypairPut old true) :=
    keypairPut_affiliation (References pid [kid]) (fun _ _ h => h.erase _) old true
  have previous := modifyPeer_slots pid [kid]
    (fun p => {p with keypairPrevious := p.keypairCurrent})
    (fun _ => rfl) (fun _ => rfl) (by
      intro p k h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h)))
  have current := modifyPeer_slots pid [kid]
    (fun p => {p with keypairCurrent := some kid, keypairNext := none})
    (fun _ => rfl) (fun _ => rfl) (by
      intro p k h
      rcases h with h | h | h
      · exact Or.inr (Or.inr (Or.inr (by simpa using h.symm)))
      · exact Or.inr (Or.inl h)
      · cases h)
  unfold receivedWithKeypair
  apply preserves_bind readPeer
  intro p
  apply preserves_bind (ambient .receivedNotNew (p.keypairNext != some kid))
  intro notNew
  cases notNew with
  | true => exact preserves_pure false
  | false =>
    apply preserves_bind readPeer
    intro q
    apply preserves_bind (ambient .receivedChanged (q.keypairNext != some kid))
    intro changed
    cases changed with
    | true => exact preserves_pure false
    | false =>
      apply preserves_bind readPeer
      intro old
      apply preserves_bind previous
      intro _
      apply preserves_bind (put old.keypairPrevious)
      intro _
      apply preserves_bind current
      intro _
      exact preserves_pure true

/-- A normal responder promotion obtains its new current reference from the
actual first next-slot read. No separately supplied packet-key premise is needed. -/
theorem receivedWithKeypair_preserves (pid : PeerId) (kid : KeypairId) :
    Preserves Inv (receivedWithKeypair pid kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have whole := hr
  simp only [receivedWithKeypair,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,u,middle,read,notNew,t,afterBranch,branchRun,tail⟩ := hr
  obtain ⟨sameWorld,sameAmbient,d,hd,hp⟩ := Origins.getPeer_return _ _ _ _ _ _ read
  subst u
  subst middle
  have actual := (hoare_iff_run_ambient _ _ _).mp
    (Queues.RxCredits.branch_predicate_native (fun g => g = w) .receivedNotNew
      (p.keypairNext != some kid)) w a notNew t afterBranch rfl branchRun
  rcases actual with ⟨decision,same⟩
  subst t
  cases notNew with
  | true =>
    simp only [ite_true,StateT.run_pure,CounterWindow.except_pure,Except.ok.injEq,Prod.mk.injEq] at tail
    rcases tail with ⟨⟨rfl,rfl⟩,rfl⟩
    exact hi
  | false =>
    have next : p.keypairNext = some kid := by simpa using decision.symm
    have refs : References pid [kid] (view w) := by
      intro s hs
      have eq : s = state d := Option.some.inj (hs.symm.trans (by simp [view,hd]))
      subst s
      refine ⟨hi _ hs,?_⟩
      intro k hk
      have same : k = kid := by simpa using hk
      subst k
      exact hi _ hs pid (peerCell p) kid (by simp [state,hp]) (Or.inr (Or.inr next))
    have final := (hoare_iff_run_ambient _ _ _).mp
      (received_references pid kid) w a result v b refs whole
    exact fun s hs => (final s hs).1

end Leanux.Proofs.WG.CurrentSlots
