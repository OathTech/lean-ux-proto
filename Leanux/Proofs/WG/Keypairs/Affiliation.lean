import Leanux.Proofs.WG.Peers.Affiliation
import Leanux.Proofs.WG.Lifetimes.KeypairAllocation
import Leanux.Proofs.Framing.WGHandshake

/-! Fresh nullable key allocation and source-derived key-slot compatibility.
NULL is an admissible allocation argument; freshness follows from bounds on
all existing key references, rather than distinctness of a peer's slots. -/
namespace Leanux.Proofs.WG.Affiliation
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

def State.allocate (s : State) (stamp : Nat) (word : Option PeerId) : State :=
  {s with
    nextKey := s.nextKey + 1
    keys := fun q => if q = s.nextKey then some (stamp, word) else s.keys q}

theorem State.Inv.allocate {s : State} (hi : s.Inv) (stamp : Nat) (word : Option PeerId)
    (hb : ∀ pid, word = some pid → pid < s.nextPeer) : (s.allocate stamp word).Inv := by
  have refs (pid kid) (hr : s.keyRef pid kid) : (s.allocate stamp word).keyRef pid kid := by
    refine ⟨by exact Nat.lt_trans hr.1 (Nat.lt_succ_self _), ?_⟩
    intro st wd hk
    exact hr.2 _ _ (by simpa [State.allocate, Nat.ne_of_lt hr.1] using hk)
  constructor
  · exact hi.peerBound
  · intro kid k hk
    by_cases he : kid = s.nextKey
    · subst kid; exact Nat.lt_succ_self _
    · have old := hi.keyBound kid k (by simpa [State.allocate, he] using hk)
      exact Nat.lt_trans old (Nat.lt_succ_self _)
  · exact hi.self
  · intro kid st pid hk
    by_cases he : kid = s.nextKey
    · simp [State.allocate, he] at hk
      exact hb pid hk.2
    · exact hi.words _ _ _ (by simpa [State.allocate, he] using hk)
  · intro pid p kid hp hs; exact refs _ _ (hi.slots _ _ _ hp hs)
  · intro id pid kid hp; exact ⟨(hi.tx _ _ _ hp).1, refs _ _ (hi.tx _ _ _ hp).2⟩
  · intro id pid kid hp; exact ⟨(hi.rx _ _ _ hp).1, refs _ _ (hi.rx _ _ _ hp).2⟩

theorem allocation_state (d : Device) (stamp : Nat) (word : Option PeerId) :
    state (Lifetimes.keyAllocationDevice d stamp word) = (state d).allocate stamp word := by
  unfold state Lifetimes.keyAllocationDevice State.allocate
  congr 1
  funext q
  by_cases he : q = d.nextKeypairId
  · simp [he, keyCell]
  · simp [Std.TreeMap.getElem?_insert, he, Ne.symm he]

def CreationInput (word : Option PeerId) (w : WGWorld) : Prop :=
  Inv w ∧ ∀ s pid, view w = some s → word = some pid → pid < s.nextPeer

/-- The original core returns a resident key with the requested nullable word
and a slot below the advanced frontier. The exact endpoint is supplied by
`Lifetimes.keypairCreateCore_run`. -/
theorem keypairCreateCore_affiliation (word : Option PeerId) :
    ⦃fun w => ⌜CreationInput word w⌝⦄ Lifetimes.keypairCreateCore word
    ⦃⇓? kid w => ⌜Inv w ∧ ∃ s stamp, view w = some s ∧
      s.keys kid = some (stamp, word) ∧ kid < s.nextKey⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient kid v ambient' hi hr
  rw [Lifetimes.keypairCreateCore_run] at hr
  cases hd : w.dev with
  | none => simp [hd] at hr
  | some d =>
    simp only [hd, Except.ok.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    have hs : view w = some (state d) := by simp [view, hd]
    have hv : view (Lifetimes.keyAllocationWorld w d word) =
        some ((state d).allocate (w.keypairCounter + 1) word) := by
      simp [view, Lifetimes.keyAllocationWorld, allocation_state]
    have hn := (hi.1 _ hs).allocate (w.keypairCounter + 1) word (fun pid hp => hi.2 _ pid hs hp)
    refine ⟨?_, _, w.keypairCounter + 1, hv, ?_, ?_⟩
    · intro s he; rw [hv] at he; cases he; exact hn
    · simp [State.allocate, state]
    · exact Nat.lt_succ_self _

/-- Allocation refusal is included; hidden-input Stops have no final WGWorld. -/
theorem keypairCreate_affiliation (word : Option PeerId) :
    ⦃fun w => ⌜CreationInput word w⌝⦄ keypairCreate word
    ⦃⇓? result w => ⌜Inv w ∧ ∀ kid, result = some kid →
      ∃ s stamp, view w = some s ∧ s.keys kid = some (stamp, word) ∧ kid < s.nextKey⌝⦄ := by
  rw [Lifetimes.keypairCreate_factor]
  have ha {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (CreationInput word) (fun _ => CreationInput word) :=
    hoare_liftAmbient a (CreationInput word)
  unfold Hoare at ha
  have hc := keypairCreateCore_affiliation word
  mvcgen [-Std.Do.Spec.monadLift_StateT, ha, hc, branch, hiddenAlloc]
  all_goals simp_all [CreationInput, Inv]

/-- Nullable slot compatibility supplies identity only when the actual word is
non-NULL; no residency of its peer is inferred. -/
theorem slot_word (w : WGWorld) (pid : PeerId) (p : Peer) (kid : KeypairId) (k : Keypair)
    (hi : Inv w) (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (hs : p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid)
    (hk : d.keypairs[kid]? = some k) : Compatible k.peer pid := by
  have inv := hi (state d) (by simp [view, hd])
  exact (inv.slots pid (peerCell p) kid (by simp [state, hp]) hs).2 k.internalId k.peer
    (by simp [state, hk, keyCell])


theorem keyAt_view (w : WGWorld) (kid : KeypairId) :
    keyAt w kid = (view w).bind (fun s => s.keys kid) := by
  cases h : w.dev <;> simp [keyAt, view, state, h]

theorem keypairGet_affiliation (kp : Option KeypairId) (s : Option State) :
    ⦃fun w => ⌜view w = s⌝⦄ keypairGet kp
    ⦃⇓? result w => ⌜view w = s ∧ (result = none ∨ result = kp)⌝⦄ := by
  have hg := fun id => getKeypair_spec (fun t => t = s) id
  have hs := fun id k => setKeypair_spec (fun t => t = s) id k
  mvcgen [keypairGet, hg, hs, branch, branchCmp, refcountIncNotZero,
    invariant, unsupported, AmbientM.branch, AmbientM.branchCmp,
    AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [keyCell, keyAt_view, view]
  all_goals grind

/-- Erasing a key preserves every nullable reference: absent slots are allowed. -/
def State.eraseKey (s : State) (kid : KeypairId) : State :=
  {s with keys := fun q => if q = kid then none else s.keys q}

theorem State.Inv.eraseKey {s : State} (hi : s.Inv) (kid : KeypairId) : (s.eraseKey kid).Inv := by
  have refs (pid k) (hr : s.keyRef pid k) : (s.eraseKey kid).keyRef pid k := by
    refine ⟨hr.1, ?_⟩
    intro stamp word hk
    by_cases he : k = kid
    · simp [State.eraseKey, he] at hk
    · exact hr.2 _ _ (by simpa [State.eraseKey, he] using hk)
  constructor
  · exact hi.peerBound
  · intro k key hk
    by_cases he : k = kid
    · simp [State.eraseKey, he] at hk
    · exact hi.keyBound _ _ (by simpa [State.eraseKey, he] using hk)
  · exact hi.self
  · intro k stamp pid hk
    by_cases he : k = kid
    · simp [State.eraseKey, he] at hk
    · exact hi.words _ _ _ (by simpa [State.eraseKey, he] using hk)
  · intro pid p k hp hs; exact refs _ _ (hi.slots _ _ _ hp hs)
  · intro id pid k hp; exact ⟨(hi.tx _ _ _ hp).1, refs _ _ (hi.tx _ _ _ hp).2⟩
  · intro id pid k hp; exact ⟨(hi.rx _ _ _ hp).1, refs _ _ (hi.rx _ _ _ hp).2⟩


theorem eraseKey_state (d : Device) (kid : KeypairId) :
    state {d with keypairs := d.keypairs.erase kid} = (state d).eraseKey kid := by
  unfold state State.eraseKey
  congr 1
  funext q
  by_cases he : q = kid
  · simp [he]
  · simp [Std.TreeMap.getElem?_erase, he, Ne.symm he]

theorem eraseKey_spec (P : Option State → Prop)
    (closed : ∀ s kid, P (some s) → P (some (s.eraseKey kid))) (kid : KeypairId) :
    ⦃fun w => ⌜P (view w)⌝⦄ modifyDev (fun d => {d with keypairs := d.keypairs.erase kid})
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hp hr
  cases hr
  cases hd : w.dev with
  | none => simpa [view, modifyDev, hd] using hp
  | some d =>
    simpa [view, modifyDev, hd, eraseKey_state] using closed (state d) kid (by simpa [view, hd] using hp)

theorem index_frame {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s =>
      {wgStoreView (project s) with dev := (project s).dev.map fun (d : Device) =>
        {d with indexTable := []}}) a) :
    SameView (fun s => view (project s)) a :=
  ha.of_factor (fun k : WGStoreView => k.dev.map state) (fun s => view (project s))
    (fun s => by cases h : (project s).dev <;> simp [view, h, state])

/-- The original release only changes counts, index entries or erases a key.
The predicate may retain compatible references to erased keys. -/
theorem keypairPut_affiliation (P : Option State → Prop)
    (closed : ∀ s kid, P (some s) → P (some (s.eraseKey kid)))
    (kp : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜P (view w)⌝⦄ keypairPut kp now
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hp hr
  have hg := fun id => getKeypair_spec (fun t => t = view w) id
  have hs := fun id k => setKeypair_spec (fun t => t = view w) id k
  have hw := fun o => indexOwner_peerDeref_preserves o (fun t => view t = view w)
  have hi {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun t => view t = view w) (fun _ t => view t = view w) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa only [view, hd, Option.map_some, state] using hg
  unfold Preserves Hoare at hw hi
  have he (kid) :
      ⦃fun u => ⌜view u = view w⌝⦄ modifyDev (fun d => {d with keypairs := d.keypairs.erase kid})
      ⦃⇓? _ u => ⌜P (view u)⌝⦄ := by
    exact hoare_consequence (eraseKey_spec P closed kid)
      (fun _ hv => hv ▸ hp) (fun _ _ h => h)
  have spec : ⦃fun u => ⌜view u = view w⌝⦄ keypairPut kp now ⦃⇓? _ u => ⌜P (view u)⌝⦄ := by
    mvcgen [keypairPut, hg, hs, hw, hi, he, branch, branchCmp, refcountDecAndTest,
      invariant, unsupported, AmbientM.branch, AmbientM.branchCmp,
      AmbientM.invariant, AmbientM.unsupported]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [keyCell, keyAt_view, view]
    all_goals grind
  exact (hoare_iff_run_ambient _ _ _).mp spec w ambient result v ambient' rfl hr


def State.setSlots (s : State) (pid : PeerId) (current previous next : Option KeypairId) : State :=
  {s with peers := fun q => if q = pid then (s.peers q).map (fun p => (p.1, p.2.1, current, previous, next)) else s.peers q}

theorem State.Inv.setSlots {s : State} (hi : s.Inv) (pid : PeerId)
    (current previous next : Option KeypairId)
    (refs : ∀ kid, current = some kid ∨ previous = some kid ∨ next = some kid → s.keyRef pid kid) :
    (s.setSlots pid current previous next).Inv := by
  constructor
  · intro q p hp
    by_cases he : q = pid
    · subst q; simp only [State.setSlots, ite_true] at hp
      obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact hi.peerBound _ _ ho
    · exact hi.peerBound _ _ (by simpa [State.setSlots, he] using hp)
  · exact hi.keyBound
  · intro q p hp
    by_cases he : q = pid
    · subst q; simp only [State.setSlots, ite_true] at hp
      obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact hi.self pid old ho
    · exact hi.self _ _ (by simpa [State.setSlots, he] using hp)
  · exact hi.words
  · intro q p kid hp hs
    by_cases he : q = pid
    · subst q; simp only [State.setSlots, ite_true] at hp
      obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact refs kid hs
    · exact hi.slots _ _ _ (by simpa [State.setSlots, he] using hp) hs
  · exact hi.tx
  · exact hi.rx

def References (pid : PeerId) (keys : List KeypairId) (v : Option State) : Prop :=
  ∀ s, v = some s → s.Inv ∧ ∀ kid ∈ keys, s.keyRef pid kid

theorem References.erase (h : References pid keys (some s)) (kid : KeypairId) :
    References pid keys (some (s.eraseKey kid)) := by
  intro t ht
  cases ht
  refine ⟨(h s rfl).1.eraseKey kid, ?_⟩
  intro k hk
  have old := (h s rfl).2 k hk
  refine ⟨old.1, ?_⟩
  intro stamp word hw
  by_cases he : k = kid
  · simp [State.eraseKey, he] at hw
  · exact old.2 _ _ (by simpa [State.eraseKey, he] using hw)

/-- Fresh get/set of all three slots, also covering aliasing among old slots. -/
def setSlots (pid : PeerId) (current previous next : Option KeypairId) : WG.M Unit := do
  let p ← getPeer pid
  setPeer pid {p with keypairCurrent := current, keypairPrevious := previous, keypairNext := next}

theorem setSlots_spec (pid : PeerId) (keys : List KeypairId) (current previous next : Option KeypairId)
    (members : ∀ kid, current = some kid ∨ previous = some kid ∨ next = some kid → kid ∈ keys) :
    ⦃fun w => ⌜References pid keys (view w)⌝⦄ setSlots pid current previous next
    ⦃⇓? _ w => ⌜References pid keys (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  cases hd : w.dev with
  | none => simp [setSlots, getPeer, getDev, hd, invariant, AmbientM.invariant] at hr; cases hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [setSlots, getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr; cases hr
    | some p =>
      simp [setSlots, getPeer, getDev, hd, hp, setPeer, modifyDev] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hs : state {d with peers := d.peers.insert pid {p with keypairCurrent := current, keypairPrevious := previous, keypairNext := next}} = (state d).setSlots pid current previous next := by
        unfold state State.setSlots
        congr 1
        funext q
        by_cases he : pid = q
        · subst q; simp [hp, peerCell]
        · simp [Std.TreeMap.getElem?_insert, he, Ne.symm he]
      have orig := hi (state d) (by simp [view, hd])
      intro s hview
      simp only [view, Option.map_some, hs, Option.some.injEq] at hview
      subst s
      exact ⟨orig.1.setSlots pid current previous next (fun kid hh => orig.2 kid (members kid hh)), orig.2⟩


/-- The actual private fresh-get modifier, for updates selecting only old slots
or explicitly retained compatible keys. No distinctness of slots is required. -/
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
      refine ⟨orig.1.setSlots pid _ _ _ ?_, orig.2⟩
      intro kid hh
      rcases slots p kid hh with hc | hp' | hn | hk
      · exact orig.1.slots pid (peerCell p) kid (by simp [state, hp]) (Or.inl hc)
      · exact orig.1.slots pid (peerCell p) kid (by simp [state, hp]) (Or.inr (Or.inl hp'))
      · exact orig.1.slots pid (peerCell p) kid (by simp [state, hp]) (Or.inr (Or.inr hn))
      · exact orig.2 kid hk

def peerKeys (p : Peer) : List KeypairId :=
  p.keypairCurrent.toList ++ p.keypairPrevious.toList ++ p.keypairNext.toList

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
    apply (hg.1 s hs).1.slots pid (peerCell p) kid hp
    simpa [peerKeys, peerCell, List.mem_append, Option.mem_toList] using hk


/-- Literal original rotation after the saved initial peer getter. -/
def rotateSource (pid : PeerId) (kid : KeypairId) (p : Peer) : WG.M Unit := do
  let (previous, next, current) := (p.keypairPrevious, p.keypairNext, p.keypairCurrent)
  if ← branch .addKeypairInitiator (← getKeypair kid).iAmTheInitiator then
    if ← branch .addKeypairHasNext next.isSome then
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid fun p => {p with keypairNext := none, keypairPrevious := next}
      keypairPut current true
    else
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid fun p => {p with keypairPrevious := current}
    keypairPut previous true
    (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid fun p => {p with keypairCurrent := some kid}
  else
    (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid fun p => {p with keypairNext := some kid}
    keypairPut next true
    (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid fun p => {p with keypairPrevious := none}
    keypairPut previous true

theorem rotateSource_eq (pid kid : Nat) :
    addNewKeypair pid kid = (do let p ← getPeer pid; rotateSource pid kid p) := rfl

theorem rotateSource_affiliation (pid kid : Nat) (p : Peer) :
    ⦃fun w => ⌜References pid ([kid] ++ peerKeys p) (view w)⌝⦄ rotateSource pid kid p
    ⦃⇓? _ w => ⌜References pid ([kid] ++ peerKeys p) (view w)⌝⦄ := by
  let keys := [kid] ++ peerKeys p
  have hkey := getKeypair_spec (References pid keys) kid
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
  mvcgen [rotateSource, hkey, hp, h1, h2, h3, h4, h5, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [References, view]

/-- Actual original rotation under nullable compatibility of the incoming key.
Old slots may alias or already name absent keys; original getters may Stop. -/
theorem addNewKeypair_affiliation (pid : PeerId) (kid : KeypairId) :
    ⦃fun w => ⌜References pid [kid] (view w)⌝⦄ addNewKeypair pid kid
    ⦃⇓? _ w => ⌜Inv w⌝⦄ := by
  rw [rotateSource_eq]
  have hg := getPeer_references pid [kid]
  have ht := rotateSource_affiliation pid kid
  mvcgen [hg, ht]
  all_goals simp_all [References, Inv]


theorem handshake_creation_input (pid : PeerId) :
    ⦃fun w => ⌜Inv w⌝⦄ IndexOwner.peerWord (.handshake pid)
    ⦃⇓? word w => ⌜CreationInput word w ∧ Compatible word pid⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient word v ambient' hi hr
  have hg := (hoare_iff_run_ambient _ _ _).mp
    (peerWord_spec (.handshake pid) (fun t => ∀ s, t = some s → s.Inv))
    w ambient word v ambient' hi hr
  obtain ⟨s, hs, hw⟩ := Option.bind_eq_some_iff.mp hg.2
  obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hw
  have hc : Compatible word pid := he ▸ (hg.1 s hs).self pid p hp
  refine ⟨⟨hg.1, ?_⟩, hc⟩
  intro t q ht hword
  have eqs : t = s := Option.some.inj (ht.symm.trans hs)
  subst t
  have eqp : q = pid := by simpa [Compatible, hword] using hc
  subst q
  exact (hg.1 s hs).peerBound pid p hp

theorem keypairCreate_for_peer (pid : PeerId) (word : Option PeerId) :
    ⦃fun w => ⌜CreationInput word w ∧ Compatible word pid⌝⦄ keypairCreate word
    ⦃⇓? result w => ⌜Inv w ∧ ∀ kid, result = some kid → References pid [kid] (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have hc := (hoare_iff_run_ambient _ _ _).mp (keypairCreate_affiliation word)
    w ambient result v ambient' hi.1 hr
  refine ⟨hc.1, ?_⟩
  intro kid hkid
  obtain ⟨s, stamp, hs, hk, hb⟩ := hc.2 kid hkid
  intro t ht
  have he : t = s := Option.some.inj (ht.symm.trans hs)
  subst t
  refine ⟨hc.1 s hs, ?_⟩
  intro k hmem
  have he : k = kid := by simpa using hmem
  subst k
  refine ⟨hb, ?_⟩
  intro st wd hw
  rw [hk] at hw
  have he := congrArg Prod.snd (Option.some.inj hw)
  have heq : word = wd := he
  exact heq ▸ hi.2

theorem deriveKeys_view (kid : KeypairId) (initiator : Bool) (ck : List UInt8) :
    SameView view (deriveKeys kid initiator ck) := by
  apply SameView.of_wp
  intro s
  have hg := getKeypair_spec (fun t => t = s) kid
  have hs := fun k => setKeypair_spec (fun t => t = s) kid k
  have hc {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => view w = s) (fun _ w => view w = s) :=
    hoare_liftAmbient a (fun w => view w = s)
  have hk := fun b c ck d => (kdf_sameWGWorld b c ck d).wp (fun w => view w = s)
  have ho := fun xs i => (kdfOut_sameWGWorld xs i).wp (fun w => view w = s)
  unfold Hoare at hc
  mvcgen [-Std.Do.Spec.monadLift_StateT, deriveKeys, hg, hs, hc, hk, ho, hiddenClock64]
  all_goals split <;> simp_all [keyCell]

theorem handshakeZero_view (pid : PeerId) : SameView view (handshakeZero pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_spec (fun t => t = s) pid
  have hs := fun p => setPeer_spec (fun t => t = s) pid p
  mvcgen [handshakeZero, hg, hs]


/-- The original post-allocation session suffix, with fresh source getters. -/
def sessionTail (pid st kp : Nat) : WG.M Bool := do
  let p ← getPeer pid
  let initiator := st == HANDSHAKE_CONSUMED_RESPONSE
  setKeypair kp {(← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex := p.remoteIndex}
  if ← branch .sessionInitiator initiator then deriveKeys kp true p.chainingKey
  else deriveKeys kp false p.chainingKey
  handshakeZero pid
  if ← branch .sessionAlive !(← getPeer pid).isDead then
    addNewKeypair pid kp
    _ ← IndexOwner.peerDeref (.handshake pid)
    if !(← indexReplaceHandshake pid kp) then unsupported "begin_session: the handshake entry was unhashed"
    return true
  unsupported "a dead peer finishing a session"

theorem sessionTail_eq (pid : PeerId) : beginSession pid = (do
    let st := (← getPeer pid).handshakeState
    if ← WG.andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
        (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE)) then return false
    let created ← keypairCreate (← IndexOwner.peerWord (.handshake pid))
    if ← branch .sessionNoKeypair created.isNone then return false
    let some kp := created | invariant "unreachable"
    sessionTail pid st kp) := rfl

theorem sessionTail_affiliation (pid st kp : Nat) :
    ⦃fun w => ⌜References pid [kp] (view w)⌝⦄ sessionTail pid st kp
    ⦃⇓? _ w => ⌜Inv w⌝⦄ := by
  have hg := getPeer_spec (References pid [kp]) pid
  have hk := getKeypair_spec (References pid [kp]) kp
  have hs := fun k => setKeypair_spec (References pid [kp]) kp k
  have hd := fun b ck => (deriveKeys_view kp b ck).wp (References pid [kp])
  have hz := (handshakeZero_view pid).wp (References pid [kp])
  have ha := addNewKeypair_affiliation pid kp
  have hf := indexOwner_peerDeref_preserves (.handshake pid) Inv
  have hi : Hoare (MonadLift.monadLift (indexReplaceHandshake pid kp) : WG.M Bool) Inv (fun _ => Inv) := by
    apply hoare_liftIndex
    intro g d table h hdev
    simpa only [Inv, view, hdev, Option.map_some, state] using h
  unfold Preserves Hoare at hf hi
  mvcgen [sessionTail, hg, hk, hs, hd, hz, ha, hf, hi, branch, unsupported,
    AmbientM.branch, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Inv, References, keyAt_view, keyCell, view]
  all_goals grind

/-- The complete original session creation derives allocation compatibility
from its actual handshake-word read and carries it into original rotation. -/
theorem beginSession_affiliation (pid : PeerId) :
    ⦃fun w => ⌜Inv w⌝⦄ beginSession pid ⦃⇓? _ w => ⌜Inv w⌝⦄ := by
  rw [sessionTail_eq]
  have hg := getPeer_spec (fun t => ∀ s, t = some s → s.Inv) pid
  have hw := handshake_creation_input pid
  have hc := keypairCreate_for_peer pid
  have ht := sessionTail_affiliation pid
  mvcgen [hg, hw, hc, ht, WG.andM, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Inv, References, view]
  all_goals grind

end Leanux.Proofs.WG.Affiliation
