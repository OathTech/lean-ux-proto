import Leanux.Proofs.Framing.PeerBorrow
import Leanux.Proofs.WG.Lifetimes.LookupAccess

/-! Nullable affiliation records the embedded peer words and the references
which name their owners. Missing objects and NULL words are permitted. This is
an input invariant for local source contracts, not initialized Runner closure. -/
namespace Leanux.Proofs.WG.Affiliation
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
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
def view (w : World) : Option State := w.k.wg.map state

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

def Inv (w : World) : Prop := ∀ s, view w = some s → s.Inv

def peerAt (w : World) (pid : PeerId) := w.k.wg.bind fun d => d.peers[pid]?.map peerCell
def keyAt (w : World) (kid : KeypairId) := w.k.wg.bind fun d => d.keypairs[kid]?.map keyCell

theorem kernel (ha : SameKernel a) : SameView view a :=
  fun w x v hr => congrArg (fun k : Kernel => k.wg.map state) (ha w x v hr)

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
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals simp_all [peerAt]

theorem setPeer_spec (P : Option State → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (view w) ∧ peerAt w pid = some (peerCell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  cases hd : w.k.wg with
  | none => simp [peerAt, hd] at hi
  | some d =>
    obtain ⟨old, hold, he⟩ := Option.map_eq_some_iff.mp (by simpa [peerAt, hd] using hi.2)
    have hh := state_peer_same d pid old p hold he.symm
    cases hr
    simpa [view, setPeer, modifyDev, modifyK, hd, hh] using hi.1

theorem getKeypair_spec (P : Option State → Prop) (kid : KeypairId) :
    ⦃fun w => ⌜P (view w)⌝⦄ getKeypair kid
    ⦃⇓? k w => ⌜P (view w) ∧ keyAt w kid = some (keyCell k)⌝⦄ := by
  mvcgen [getKeypair, getDev, getK, invariant]
  all_goals simp_all [keyAt]

theorem setKeypair_spec (P : Option State → Prop) (kid : KeypairId) (k : Keypair) :
    ⦃fun w => ⌜P (view w) ∧ keyAt w kid = some (keyCell k)⌝⦄ setKeypair kid k
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  cases hd : w.k.wg with
  | none => simp [keyAt, hd] at hi
  | some d =>
    obtain ⟨old, hold, he⟩ := Option.map_eq_some_iff.mp (by simpa [keyAt, hd] using hi.2)
    have hh := state_key_same d kid old k hold he.symm
    cases hr
    simpa [view, setKeypair, modifyDev, modifyK, hd, hh] using hi.1

theorem peerGetMaybeZero_view (peer : Option PeerId) : SameView view (peerGetMaybeZero peer) := by
  intro w result v hr
  have hb := ((hoare_iff_triple _ _ _).mpr (PeerBorrow.acquire_spec peer w.k) w result v rfl hr).2
  cases result with
  | none => exact congrArg (fun k : Kernel => k.wg.map state) hb
  | some pid =>
    obtain ⟨d, p, hd, hp, hpos, hv⟩ := hb
    simp only [view, hv, hd, Option.map_some]
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

def wordAt (w : World) (o : IndexOwner) := (view w).bind (fun s => s.word o)

theorem peerWord_spec (o : IndexOwner) (P : Option State → Prop) :
    ⦃fun w => ⌜P (view w)⌝⦄ o.peerWord
    ⦃⇓? word w => ⌜P (view w) ∧ wordAt w o = some word⌝⦄ := by
  cases o <;> mvcgen [IndexOwner.peerWord, getPeer, getKeypair, getDev, getK, invariant]
  all_goals simp_all [wordAt, view, state, State.word, peerCell, keyCell]

theorem setPeerWord_view (o : IndexOwner) (word : Option PeerId) (w v : World)
    (hr : (o.setPeerWord word).run w = .ok ((), v)) :
    view v = (view w).map (fun s => s.setWord o word) := by
  cases hd : w.k.wg with
  | none => cases o <;> simp [IndexOwner.setPeerWord, getPeer, getKeypair, getDev, getK, hd, invariant] at hr
  | some d =>
    cases o with
    | handshake pid =>
      cases hp : d.peers[pid]? with
      | none => simp [IndexOwner.setPeerWord, getPeer, getDev, getK, hd, hp, invariant] at hr
      | some p =>
        simp [IndexOwner.setPeerWord, getPeer, getDev, getK, hd, hp, setPeer, modifyDev, modifyK] at hr
        subst v
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
      | none => simp [IndexOwner.setPeerWord, getKeypair, getDev, getK, hd, hk, invariant] at hr
      | some k =>
        simp [IndexOwner.setPeerWord, getKeypair, getDev, getK, hd, hk, setKeypair, modifyDev, modifyK] at hr
        subst v
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
def acquireOwner (owner : IndexOwner) : M (Option PeerId) := do
  let peer ← peerGetMaybeZero (← owner.peerWord)
  owner.setPeerWord peer
  return peer

def Acquisition (owner : IndexOwner) (w : World) (result : Option PeerId) (v : World) : Prop :=
  ∃ (oldWord : Option PeerId) (readWorld borrowedWorld : World),
    owner.peerWord.run w = .ok (oldWord, readWorld) ∧
    (peerGetMaybeZero oldWord).run readWorld = .ok (result, borrowedWorld) ∧
    (owner.setPeerWord result).run borrowedWorld = .ok ((), v)

theorem acquireOwner_acquisition (owner : IndexOwner) (w v : World) (result : Option PeerId)
    (hr : (acquireOwner owner).run w = .ok (result, v)) : Acquisition owner w result v := by
  simp only [acquireOwner, StateT.run_bind] at hr
  cases hread : owner.peerWord.run w with
  | error e => simp [hread] at hr
  | ok read =>
    rcases read with ⟨word, u⟩
    simp only [hread, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    cases hget : (peerGetMaybeZero word).run u with
    | error e => simp [hget] at hr
    | ok got =>
      rcases got with ⟨peer, b⟩
      simp only [hget, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
      cases hstore : (owner.setPeerWord peer).run b with
      | error e => simp [hstore] at hr
      | ok out =>
        rcases out with ⟨u, final⟩
        cases u
        simp [hstore] at hr
        rcases hr with ⟨rfl, rfl⟩
        exact ⟨word, _, _, hread, hget, hstore⟩

theorem Acquisition.facts (h : Acquisition owner w result v) :
    (result = none ∨ wordAt w owner = some result) ∧
    view v = (view w).map (fun s => s.setWord owner result) := by
  obtain ⟨oldWord, readWorld, borrowedWorld, read, get, store⟩ := h
  have rd := (hoare_iff_triple _ _ _).mpr (peerWord_spec owner (fun s => s = view w))
    w oldWord readWorld rfl read
  have gp := (hoare_iff_triple _ _ _).mpr (PeerBorrow.acquire_spec oldWord readWorld.k)
    readWorld result borrowedWorld rfl get
  have gv := peerGetMaybeZero_view oldWord readWorld result borrowedWorld get
  have ww : wordAt w owner = some oldWord := by
    simpa only [wordAt, rd.1] using rd.2
  refine ⟨gp.1.imp id (fun he => by simpa [he] using ww), ?_⟩
  rw [setPeerWord_view owner result borrowedWorld v store, gv, rd.1]

theorem acquireOwner_preserves (owner : IndexOwner) (w v : World) (result : Option PeerId)
    (hi : Inv w) (hr : (acquireOwner owner).run w = .ok (result, v)) : Inv v := by
  have facts := (acquireOwner_acquisition owner w v result hr).facts
  intro out hout
  rw [facts.2] at hout
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hout
  apply (hi s hs).setWord
  rcases facts.1 with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [wordAt, hs] using h)

theorem acquireOwner_handshake (pid borrowed : PeerId) (w v : World)
    (hi : Inv w) (hr : (acquireOwner (.handshake pid)).run w = .ok (some borrowed, v)) : borrowed = pid := by
  have facts := (acquireOwner_acquisition (.handshake pid) w v (some borrowed) hr).facts
  have hw : wordAt w (.handshake pid) = some (some borrowed) := facts.1.resolve_left (by simp)
  obtain ⟨s, hs, hh⟩ := Option.bind_eq_some_iff.mp hw
  obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hh
  have hc := (hi s hs).self pid p hp
  rcases hc with hc | hc
  · simp [State.word, hc] at he
  · rw [hc] at he
    exact (Option.some.inj he).symm

theorem frame (ha : SameView view a) : ⦃fun w => ⌜Inv w⌝⦄ a ⦃⇓? _ w => ⌜Inv w⌝⦄ :=
  ha.wp (fun v => ∀ s, v = some s → s.Inv)

theorem acquireOwner_spec (owner : IndexOwner) :
    ⦃fun w => ⌜Inv w⌝⦄ acquireOwner owner
    ⦃⇓? result w => ⌜Inv w ∧ ∀ pid borrowed,
      owner = .handshake pid → result = some borrowed → borrowed = pid⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w result v hi hr
  refine ⟨acquireOwner_preserves owner w v result hi hr, ?_⟩
  intro pid borrowed he hn
  subst owner; subst result
  exact acquireOwner_handshake pid borrowed w v hi hr

/-- Literal original scan, with only its already-present acquisition named. -/
def indexLookupSource (kinds : List IndexKind) (index : Nat) : M (Option (IndexOwner × PeerId)) := do
  let mut entry : Option IndexEntry := none
  let mut stopped := false
  for e in ← indexBucket index do
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
  have hb := fun decision value => frame (kernel (sameKernel_branch decision value))
  have hi := frame (kernel (indexBucket_sameKernel index))
  have ha := acquireOwner_spec
  mvcgen [indexLookupSource, hb, hi, ha, invariant]
  all_goals try exact ((⇓? _ w => ⌜Inv w⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals grind

end Leanux.Proofs.WG.Affiliation
