import Leanux.Proofs.Framing.PeerBorrow
import Leanux.Proofs.WG.Lifetimes.LookupAccess

/-! Nullable affiliation records the embedded peer words and the references
which name their owners. Missing objects and NULL words are permitted. This is
an input invariant for local source contracts, not initialized Runner closure. -/
namespace Leanux.Proofs.WG.Affiliation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-- A failed get may clear the word; a successful get cannot redirect it. -/
def Compatible (word : Option PeerId) (pid : PeerId) : Prop :=
  word = none ∨ word = some pid

def peerCell (p : Peer) :=
  (p.internalId, p.handshakeEntryPeer, p.keypairCurrent, p.keypairPrevious, p.keypairNext)
def keyCell (k : Keypair) := (k.internalId, k.peer)

structure State where
  epoch : Nat
  nextPeer : Nat
  nextKey : Nat
  peers : PeerId → Option (Nat × Option PeerId × Option KeypairId × Option KeypairId × Option KeypairId)
  keys : KeypairId → Option (Nat × Option PeerId)
  tx : SkbId → Option (PeerId × KeypairId)
  rx : SkbId → Option (PeerId × KeypairId)

def state (d : Device) : State :=
  ⟨d.ifindex, d.nextPeer, d.nextKeypairId, fun i => d.peers[i]?.map peerCell,
    fun i => d.keypairs[i]?.map keyCell, fun i => d.txSkbs[i]?.map (fun p => (p.peer, p.keypair)),
    fun i => d.rxSkbs[i]?.map (fun p => (p.peer, p.keypair))⟩
def view (w : WGWorld) : Option State := w.dev.map state

def State.keyRef (s : State) (pid : PeerId) (kid : KeypairId) : Prop :=
  kid < s.nextKey ∧ ∀ stamp word, s.keys kid = some (stamp, word) → Compatible word pid

structure State.Inv (s : State) : Prop where
  peerBound : ∀ pid p, s.peers pid = some p → pid < s.nextPeer
  keyBound : ∀ kid k, s.keys kid = some k → kid < s.nextKey
  self : ∀ pid p, s.peers pid = some p → Compatible p.2.1 pid
  words : ∀ kid stamp pid, s.keys kid = some (stamp, some pid) → pid < s.nextPeer
  slots : ∀ pid p kid, s.peers pid = some p →
    (p.2.2.1 = some kid ∨ p.2.2.2.1 = some kid ∨ p.2.2.2.2 = some kid) → s.keyRef pid kid
  tx : ∀ id pid kid, s.tx id = some (pid, kid) → pid < s.nextPeer ∧ s.keyRef pid kid
  rx : ∀ id pid kid, s.rx id = some (pid, kid) → pid < s.nextPeer ∧ s.keyRef pid kid

def Inv (w : WGWorld) : Prop := ∀ s, view w = some s → s.Inv

def peerAt (w : WGWorld) (pid : PeerId) := w.dev.bind fun d => d.peers[pid]?.map peerCell
def keyAt (w : WGWorld) (kid : KeypairId) := w.dev.bind fun d => d.keypairs[kid]?.map keyCell

/-- Pure observation transport over any actual outer state and inner monad.
The seven-field premise includes the original whole-store product instances. -/
theorem kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => wgStoreView (project s)) a) :
    SameView (fun s => view (project s)) a :=
  ha.factor (fun k : WGStoreView => k.dev.map state)

theorem state_peer_same (d : Device) (pid : PeerId) (old p : Peer)
    (hp : d.peers[pid]? = some old) (he : peerCell p = peerCell old) :
    state {d with peers := d.peers.insert pid p} = state d := by
  unfold state
  congr 1
  funext q
  by_cases h : pid = q
  · subst q; simp [hp, he]
  · simp [Std.TreeMap.getElem?_insert, h]

theorem state_key_same (d : Device) (kid : KeypairId) (old k : Keypair)
    (hp : d.keypairs[kid]? = some old) (he : keyCell k = keyCell old) :
    state {d with keypairs := d.keypairs.insert kid k} = state d := by
  unfold state
  congr 1
  funext q
  by_cases h : kid = q
  · subst q; simp [hp, he]
  · simp [Std.TreeMap.getElem?_insert, h]

theorem getPeer_spec (P : Option State → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (view w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P (view w) ∧ peerAt w pid = some (peerCell p)⌝⦄ := by
  mvcgen [getPeer, getDev, invariant, AmbientM.invariant]
  all_goals simp_all [peerAt]

theorem setPeer_spec (P : Option State → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (view w) ∧ peerAt w pid = some (peerCell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  cases hd : w.dev with
  | none => simp [peerAt, hd] at hi
  | some d =>
    obtain ⟨old, hold, he⟩ := Option.map_eq_some_iff.mp (by simpa [peerAt, hd] using hi.2)
    have hh := state_peer_same d pid old p hold he.symm
    cases hr
    simpa [view, setPeer, modifyDev, hd, hh] using hi.1

theorem getKeypair_spec (P : Option State → Prop) (kid : KeypairId) :
    ⦃fun w => ⌜P (view w)⌝⦄ getKeypair kid
    ⦃⇓? k w => ⌜P (view w) ∧ keyAt w kid = some (keyCell k)⌝⦄ := by
  mvcgen [getKeypair, getDev, invariant, AmbientM.invariant]
  all_goals simp_all [keyAt]

theorem setKeypair_spec (P : Option State → Prop) (kid : KeypairId) (k : Keypair) :
    ⦃fun w => ⌜P (view w) ∧ keyAt w kid = some (keyCell k)⌝⦄ setKeypair kid k
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  cases hd : w.dev with
  | none => simp [keyAt, hd] at hi
  | some d =>
    obtain ⟨old, hold, he⟩ := Option.map_eq_some_iff.mp (by simpa [keyAt, hd] using hi.2)
    have hh := state_key_same d kid old k hold he.symm
    cases hr
    simpa [view, setKeypair, modifyDev, hd, hh] using hi.1

theorem peerGetMaybeZero_view (peer : Option PeerId) : SameView view (peerGetMaybeZero peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  have hb := ((hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec peer (wgStoreView w)) w ambient result v ambient' rfl hr).2
  change (wgStoreView v).dev.map state = (wgStoreView w).dev.map state
  cases result with
  | none => exact congrArg (fun k : WGStoreView => k.dev.map state) hb
  | some pid =>
    obtain ⟨d, p, hd, hp, hpos, hv⟩ := hb
    simp only [hv, hd, Option.map_some]
    exact congrArg some (state_peer_same d pid p {p with refcount := p.refcount + 1} hp rfl)

def State.word (s : State) : IndexOwner → Option (Option PeerId)
  | .handshake pid => (s.peers pid).map (fun p => p.2.1)
  | .keypair kid => (s.keys kid).map Prod.snd

def State.setWord (s : State) (owner : IndexOwner) (word : Option PeerId) : State :=
  match owner with
  | .handshake pid => {s with peers := fun q =>
      if q = pid then (s.peers q).map (fun p => (p.1, word, p.2.2)) else s.peers q}
  | .keypair kid => {s with keys := fun q =>
      if q = kid then (s.keys q).map (fun k => (k.1, word)) else s.keys q}

theorem Compatible.reduce (hc : Compatible old pid) (h : word = none ∨ word = old) :
    Compatible word pid := by rcases h with rfl | rfl; exact Or.inl rfl; exact hc

theorem State.Inv.setWord {s : State} (hi : s.Inv) (owner : IndexOwner) (word : Option PeerId)
    (h : word = none ∨ s.word owner = some word) : (s.setWord owner word).Inv := by
  cases owner with
  | handshake pid =>
    rcases h with rfl | h
    · constructor
      · intro q p hp
        by_cases he : q = pid
        · subst q; simp only [State.setWord, ite_true] at hp
          obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hp
          exact hi.peerBound _ _ ho
        · exact hi.peerBound _ _ (by simpa [State.setWord, he] using hp)
      · exact hi.keyBound
      · intro q p hp
        by_cases he : q = pid
        · subst q; simp only [State.setWord, ite_true] at hp
          obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hp
          exact Or.inl rfl
        · exact hi.self _ _ (by simpa [State.setWord, he] using hp)
      · exact hi.words
      · intro q p kid hp hs
        by_cases he : q = pid
        · subst q; simp only [State.setWord, ite_true] at hp
          obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hp
          exact hi.slots _ _ _ ho hs
        · exact hi.slots _ _ _ (by simpa [State.setWord, he] using hp) hs
      · exact hi.tx
      · exact hi.rx
    · have same : s.setWord (.handshake pid) word = s := by
        unfold State.word at h
        obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [State.setWord]
        have eqfun : (fun q => if q = pid then (s.peers q).map (fun old => (old.1, p.2.1, old.2.2)) else s.peers q) = s.peers := by
          funext q
          by_cases he : q = pid
          · subst q; simp [hp]
          · simp [he]
        rw [eqfun]
      simpa [same] using hi
  | keypair kid =>
    rcases h with rfl | h
    · have refs (pid k) (hr : s.keyRef pid k) : (s.setWord (.keypair kid) none).keyRef pid k := by
        refine ⟨hr.1, ?_⟩
        intro stamp word hw
        by_cases he : k = kid
        · subst k
          simp only [State.setWord, ite_true] at hw
          obtain ⟨old, ho, hh⟩ := Option.map_eq_some_iff.mp hw
          exact Or.inl (congrArg Prod.snd hh).symm
        · exact hr.2 _ _ (by simpa [State.setWord, he] using hw)
      constructor
      · exact hi.peerBound
      · intro k key hk
        by_cases he : k = kid
        · subst k
          simp only [State.setWord, ite_true] at hk
          obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hk
          exact hi.keyBound _ _ ho
        · exact hi.keyBound _ _ (by simpa [State.setWord, he] using hk)
      · exact hi.self
      · intro k stamp pid hk
        by_cases he : k = kid
        · simp [State.setWord, he] at hk
        · exact hi.words _ _ _ (by simpa [State.setWord, he] using hk)
      · intro pid p k hp hs; exact refs _ _ (hi.slots _ _ _ hp hs)
      · intro i pid k hp; exact ⟨(hi.tx _ _ _ hp).1, refs _ _ (hi.tx _ _ _ hp).2⟩
      · intro i pid k hp; exact ⟨(hi.rx _ _ _ hp).1, refs _ _ (hi.rx _ _ _ hp).2⟩
    · have same : s.setWord (.keypair kid) word = s := by
        unfold State.word at h
        obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [State.setWord]
        have eqfun : (fun q => if q = kid then (s.keys q).map (fun old => (old.1, k.2)) else s.keys q) = s.keys := by
          funext q
          by_cases he : q = kid
          · subst q; simp [hk]
          · simp [he]
        rw [eqfun]
      simpa [same] using hi

def wordAt (w : WGWorld) (o : IndexOwner) := (view w).bind (fun s => s.word o)

theorem peerWord_spec (o : IndexOwner) (P : Option State → Prop) :
    ⦃fun w => ⌜P (view w)⌝⦄ o.peerWord
    ⦃⇓? word w => ⌜P (view w) ∧ wordAt w o = some word⌝⦄ := by
  cases o <;> mvcgen [IndexOwner.peerWord, getPeer, getKeypair, getDev, invariant, AmbientM.invariant]
  all_goals simp_all [wordAt, view, state, State.word, peerCell, keyCell]

theorem setPeerWord_view (o : IndexOwner) (word : Option PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((o.setPeerWord word).run w).run ambient = .ok (((), v), ambient')) :
    view v = (view w).map (fun s => s.setWord o word) := by
  cases hd : w.dev with
  | none => cases o <;> simp [IndexOwner.setPeerWord, getPeer, getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr <;> cases hr
  | some d =>
    cases o with
    | handshake pid =>
      cases hp : d.peers[pid]? with
      | none => simp [IndexOwner.setPeerWord, getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr; cases hr
      | some p =>
        simp [IndexOwner.setPeerWord, getPeer, getDev, hd, hp, setPeer, modifyDev] at hr
        rcases hr with ⟨rfl, rfl⟩
        simp only [view, hd, Option.map_some]
        congr 1
        unfold state State.setWord
        congr 1
        funext q
        by_cases he : pid = q
        · subst q; simp [hp, peerCell]
        · simp [Std.TreeMap.getElem?_insert, he, Ne.symm he]
    | keypair kid =>
      cases hk : d.keypairs[kid]? with
      | none => simp [IndexOwner.setPeerWord, getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr; cases hr
      | some k =>
        simp [IndexOwner.setPeerWord, getKeypair, getDev, hd, hk, setKeypair, modifyDev] at hr
        rcases hr with ⟨rfl, rfl⟩
        simp only [view, hd, Option.map_some]
        congr 1
        unfold state State.setWord
        congr 1
        funext q
        by_cases he : kid = q
        · subst q; simp [hk, keyCell]
        · simp [Std.TreeMap.getElem?_insert, he, Ne.symm he]

/-- The original found-entry acquisition, before the caller's alive branch.
The owner is reread by the setter, including when it is the acquired peer. -/
def acquireOwner (owner : IndexOwner) : WG.M (Option PeerId) := do
  let peer ← peerGetMaybeZero (← owner.peerWord)
  owner.setPeerWord peer
  return peer

def Acquisition (owner : IndexOwner) (w : WGWorld) (result : Option PeerId)
    (v : WGWorld) (ambient ambient' : Ambient) : Prop :=
  ∃ (oldWord : Option PeerId) (readWorld borrowedWorld : WGWorld)
    (readAmbient borrowedAmbient : Ambient),
    (owner.peerWord.run w).run ambient = .ok ((oldWord, readWorld), readAmbient) ∧
    ((peerGetMaybeZero oldWord).run readWorld).run readAmbient =
      .ok ((result, borrowedWorld), borrowedAmbient) ∧
    ((owner.setPeerWord result).run borrowedWorld).run borrowedAmbient =
      .ok (((), v), ambient')

theorem acquireOwner_acquisition (owner : IndexOwner) (w v : WGWorld) (result : Option PeerId)
    (ambient ambient' : Ambient)
    (hr : ((acquireOwner owner).run w).run ambient = .ok ((result, v), ambient')) :
    Acquisition owner w result v ambient ambient' := by
  simp only [acquireOwner, StateT.run_bind] at hr
  cases hread : (owner.peerWord.run w).run ambient with
  | error e => simp [hread] at hr
  | ok read =>
    rcases read with ⟨⟨word, u⟩, readAmbient⟩
    simp only [hread, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    cases hget : ((peerGetMaybeZero word).run u).run readAmbient with
    | error e => simp [hget] at hr
    | ok got =>
      rcases got with ⟨⟨peer, b⟩, borrowedAmbient⟩
      simp only [hget, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
      cases hstore : ((owner.setPeerWord peer).run b).run borrowedAmbient with
      | error e => simp [hstore] at hr
      | ok out =>
        rcases out with ⟨⟨u, final⟩, finalAmbient⟩
        cases u
        simp [hstore] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨word, _, _, _, _, hread, hget, hstore⟩

theorem Acquisition.facts (h : Acquisition owner w result v ambient ambient') :
    (result = none ∨ wordAt w owner = some result) ∧
    view v = (view w).map (fun s => s.setWord owner result) := by
  obtain ⟨oldWord, readWorld, borrowedWorld, readAmbient, borrowedAmbient, read, get, store⟩ := h
  have rd := (hoare_iff_run_ambient _ _ _).mp (peerWord_spec owner (fun s => s = view w))
    w ambient oldWord readWorld readAmbient rfl read
  have gp := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec oldWord (wgStoreView readWorld))
    readWorld readAmbient result borrowedWorld borrowedAmbient rfl get
  have gv := (ProjectedAction.iff_run_ambient _ _ _).mp (peerGetMaybeZero_view oldWord)
    readWorld readAmbient result borrowedWorld borrowedAmbient get
  have ww : wordAt w owner = some oldWord := by
    simpa only [wordAt, rd.1] using rd.2
  refine ⟨gp.1.imp id (fun he => by simpa [he] using ww), ?_⟩
  rw [setPeerWord_view owner result borrowedWorld v borrowedAmbient ambient' store, gv, rd.1]

theorem acquireOwner_preserves (owner : IndexOwner) (w v : WGWorld) (result : Option PeerId)
    (ambient ambient' : Ambient)
    (hi : Inv w) (hr : ((acquireOwner owner).run w).run ambient = .ok ((result, v), ambient')) : Inv v := by
  have facts := (acquireOwner_acquisition owner w v result ambient ambient' hr).facts
  intro out hout
  rw [facts.2] at hout
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hout
  apply (hi s hs).setWord
  rcases facts.1 with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [wordAt, hs] using h)

theorem acquireOwner_handshake (pid borrowed : PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hi : Inv w) (hr : ((acquireOwner (.handshake pid)).run w).run ambient = .ok ((some borrowed, v), ambient')) : borrowed = pid := by
  have facts := (acquireOwner_acquisition (.handshake pid) w v (some borrowed) ambient ambient' hr).facts
  have hw : wordAt w (.handshake pid) = some (some borrowed) := facts.1.resolve_left (by simp)
  obtain ⟨s, hs, hh⟩ := Option.bind_eq_some_iff.mp hw
  obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hh
  have hc := (hi s hs).self pid p hp
  rcases hc with hc | hc
  · simp [hc] at he
  · rw [hc] at he
    exact (Option.some.inj he).symm

theorem frame {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => view (project s)) a) :
    ⦃fun s => ⌜Inv (project s)⌝⦄ a ⦃⇓? _ s => ⌜Inv (project s)⌝⦄ :=
  ha.wp (fun v => ∀ s, v = some s → s.Inv)

theorem acquireOwner_spec (owner : IndexOwner) :
    ⦃fun w => ⌜Inv w⌝⦄ acquireOwner owner
    ⦃⇓? result w => ⌜Inv w ∧ ∀ pid borrowed,
      owner = .handshake pid → result = some borrowed → borrowed = pid⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  refine ⟨acquireOwner_preserves owner w v result ambient ambient' hi hr, ?_⟩
  intro pid borrowed he hn
  subst owner; subst result
  exact acquireOwner_handshake pid borrowed w v ambient ambient' hi hr

/-- Literal original scan, with only its already-present acquisition named. -/
def indexLookupSource (kinds : List IndexKind) (index : Nat) : WG.M (Option (IndexOwner × PeerId)) := do
  let mut entry : Option IndexEntry := none
  let mut stopped := false
  for e in ← liftIndex (indexBucket index) do
    _ ← branch .idxWalk true
    if ← branch .idxMatch (e.index == index) then
      if ← branch .idxTypeMatch (kinds.contains e.kind) then entry := some e
      stopped := true
      break
  if !stopped then _ ← branch .idxWalk false
  if ← branch .idxFound entry.isSome then
    let some e := entry | invariant "unreachable"
    let peer ← acquireOwner e.owner
    if ← branch .idxPeerAlive peer.isSome then
      let some pid := peer | invariant "unreachable"
      return some (e.owner, pid)
  return none

theorem indexLookupSource_eq (kinds : List IndexKind) (index : Nat) :
    indexLookupSource kinds index = indexLookup kinds index := by
  simp only [indexLookupSource, indexLookup, acquireOwner, bind_assoc, pure_bind]
  rfl

theorem indexLookup_spec (kinds : List IndexKind) (index : Nat) :
    ⦃fun w => ⌜Inv w⌝⦄ indexLookup kinds index
    ⦃⇓? result w => ⌜Inv w ∧ ∀ owner borrowed,
      result = some (.handshake owner, borrowed) → borrowed = owner⌝⦄ := by
  rw [← indexLookupSource_eq]
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) Inv (fun _ => Inv) :=
    hoare_liftAmbient a Inv
  have hi : Hoare (liftIndex (indexBucket index)) Inv (fun _ => Inv) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa only [Inv, view, hd, Option.map_some, state] using hg
  have ha := acquireOwner_spec
  unfold Hoare at ambient hi
  mvcgen [-Std.Do.Spec.monadLift_StateT, indexLookupSource, branch, ambient, hi, ha,
    invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜Inv w⌝) :
    PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals grind

end Leanux.Proofs.WG.Affiliation
