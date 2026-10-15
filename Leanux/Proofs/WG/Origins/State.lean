import Leanux.Proofs.WG.Keypairs.SessionOrigin
import Leanux.Proofs.Framing.WGKernel

/-! Receiving-material support uses one actual completed session-front witness.
The nullable owner may be kept or cleared. Neither material nor owner can choose
an independent origin, and neither residence nor validity must persist. -/
namespace Leanux.Proofs.WG.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged MaterialOrigin
open Leanux.Proofs.Framing Std.Do
set_option pp.structureInstances false

/-- Clearing an owner loses information; it cannot install another owner. -/
def WordLe (current original : Option PeerId) : Prop :=
  current = none ∨ current = original

theorem WordLe.refl (word : Option PeerId) : WordLe word word := Or.inr rfl

theorem WordLe.trans (hab : WordLe a b) (hbc : WordLe b c) : WordLe a c := by
  rcases hab with rfl | rfl
  · exact Or.inl rfl
  · exact hbc

theorem WordLe.some (h : WordLe (some pid) word) : word = some pid := by
  rcases h with h | h
  · cases h
  · exact h.symm

/-- Full records are retained in the view, so a frame cannot accidentally erase
an owner/material mutation by projecting only allocation stamps. -/
abbrev View := Option (Nat × (KeypairId → Option Keypair))
def view (w : World) : View := w.k.wg.map fun d => (d.ifindex, fun id => d.keypairs[id]?)

def KeyLe (current original : Keypair) : Prop :=
  material current = material original ∧ WordLe current.peer original.peer

def RetainsView (before after : View) : Prop :=
  ∀ epoch keys, after = some (epoch, keys) →
    ∀ id k, keys id = some k → k.receiving.isValid = true →
      ∃ oldKeys old, before = some (epoch, oldKeys) ∧ oldKeys id = some old ∧
        old.receiving.isValid = true ∧ KeyLe k old

def Retains (before after : World) : Prop := RetainsView (view before) (view after)

theorem KeyLe.refl (k : Keypair) : KeyLe k k := ⟨rfl, WordLe.refl _⟩

theorem KeyLe.trans (hab : KeyLe a b) (hbc : KeyLe b c) : KeyLe a c :=
  ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

theorem RetainsView.refl (v : View) : RetainsView v v := by
  intro epoch keys hv id k hk valid
  exact ⟨keys, k, hv, hk, valid, KeyLe.refl _⟩

theorem RetainsView.trans (hab : RetainsView a b) (hbc : RetainsView b c) : RetainsView a c := by
  intro epoch keys hc id k hk valid
  obtain ⟨midKeys, mid, hb, hm, vm, km⟩ := hbc epoch keys hc id k hk valid
  obtain ⟨oldKeys, old, ha, ho, vo, ko⟩ := hab epoch midKeys hb id mid hm vm
  exact ⟨oldKeys, old, ha, ho, vo, km.trans ko⟩

theorem Retains.refl (w : World) : Retains w w := RetainsView.refl _
theorem Retains.trans (hab : Retains a b) (hbc : Retains b c) : Retains a c :=
  RetainsView.trans hab hbc

theorem retains_absent (v : View) : RetainsView v none := by
  intro epoch keys h; cases h

/-- An invalid inserted record needs no origin. All other valid records retain
exact material/owner, even when an invalid allocation overwrites an old slot. -/
theorem retains_insert (epoch : Nat) (keys : KeypairId → Option Keypair)
    (id : KeypairId) (k : Keypair)
    (hk : k.receiving.isValid = true → ∃ old, keys id = some old ∧
      old.receiving.isValid = true ∧ KeyLe k old) :
    RetainsView (some (epoch, keys))
      (some (epoch, fun q => if id = q then some k else keys q)) := by
  intro e ks he q key hq valid
  cases he
  by_cases h : id = q
  · subst q
    simp only [↓reduceIte, Option.some.injEq] at hq
    subst key
    obtain ⟨old, ho, vo, ko⟩ := hk valid
    exact ⟨keys, old, rfl, ho, vo, ko⟩
  · simp only [h, ↓reduceIte] at hq
    exact ⟨keys, key, rfl, hq, valid, KeyLe.refl _⟩

theorem retains_erase (epoch : Nat) (keys : KeypairId → Option Keypair) (id : KeypairId) :
    RetainsView (some (epoch, keys))
      (some (epoch, fun q => if id = q then none else keys q)) := by
  intro e ks he q key hq valid
  cases he
  by_cases h : id = q
  · simp [h] at hq
  · exact ⟨keys, key, rfl, by simpa [h] using hq, valid, KeyLe.refl _⟩

/-- One successful original front, its full Context and returned World support
this exact resident allocation/material and its keep-or-clear owner word. -/
def Supported (history : List SessionOrigin.Receipt) (epoch : Nat)
    (slot : KeypairId) (key : Keypair) : Prop :=
  ∃ (pid : PeerId) (run : RunWitness (Option SessionOrigin.Context))
    (ctx : SessionOrigin.Context) (d : Device) (original : Keypair),
    SessionOrigin.Receipt.material pid run ∈ history ∧
    run.Valid (SessionOrigin.front pid) ∧ run.value = some ctx ∧ ctx.slot = slot ∧
    run.after.k.wg = some d ∧ d.ifindex = epoch ∧ d.keypairs[slot]? = some original ∧
    original.receiving.isValid = true ∧ original.peer = ctx.word ∧
    material key = material original ∧ WordLe key.peer ctx.word

def InvView (history : List SessionOrigin.Receipt) (v : View) : Prop :=
  ∀ epoch keys, v = some (epoch, keys) →
    ∀ id key, keys id = some key → key.receiving.isValid = true → Supported history epoch id key

def Inv (history : List SessionOrigin.Receipt) (w : World) : Prop := InvView history (view w)

theorem Supported.mono (h : Supported xs epoch slot k) (hm : ∀ r ∈ xs, r ∈ ys) :
    Supported ys epoch slot k := by
  obtain ⟨pid, run, ctx, d, original, hin, rest⟩ := h
  exact ⟨pid, run, ctx, d, original, hm _ hin, rest⟩

theorem Supported.retain (h : Supported xs epoch slot old) (hk : KeyLe k old) :
    Supported xs epoch slot k := by
  obtain ⟨pid, run, ctx, d, original, hin, hv, hc, hs, hd, he, ho, valid, word, mat, keep⟩ := h
  exact ⟨pid, run, ctx, d, original, hin, hv, hc, hs, hd, he, ho, valid, word,
    hk.1.trans mat, hk.2.trans keep⟩

theorem InvView.retain (hi : InvView h before) (hr : RetainsView before after) : InvView h after := by
  intro epoch keys hv id k hk valid
  obtain ⟨oldKeys, old, hb, ho, vo, ko⟩ := hr epoch keys hv id k hk valid
  exact (hi epoch oldKeys hb id old ho vo).retain ko

theorem Inv.retain (hi : Inv h w) (hr : Retains w v) : Inv h v := InvView.retain hi hr

theorem InvView.mono (hi : InvView xs v) (hm : ∀ r ∈ xs, r ∈ ys) : InvView ys v :=
  fun epoch keys hv id k hk valid => (hi epoch keys hv id k hk valid).mono hm

theorem Inv.mono (hi : Inv xs w) (hm : ∀ r ∈ xs, r ∈ ys) : Inv ys w := InvView.mono hi hm

theorem inv_empty_absent (hw : w.k.wg = none) : Inv [] w := by
  intro epoch keys h; simp [view, hw] at h

/-- Canonical complete-WG and kernel frames discharge this material state
without a second hierarchy of filesystem/environment frames. -/
theorem sameView_of_sameWG (ha : SameWGKernel a) : SameView view a :=
  ha.of_factor (fun v => v.wg.map fun d => (d.ifindex, fun id => d.keypairs[id]?)) view (fun _ => rfl)

theorem retains_of_sameView (ha : SameView view a) (hr : a.run w = .ok (x,v)) : Retains w v := by
  have hv := ha w x v hr
  unfold Retains
  rw [hv]
  exact RetainsView.refl _

def Stable (P : View → Prop) : Prop := ∀ a b, RetainsView a b → P a → P b

theorem inv_stable (h : List SessionOrigin.Receipt) : Stable (InvView h) :=
  fun _ _ hr hi => hi.retain hr

def keyAt (v : View) (id : KeypairId) : Option Keypair := v.bind fun s => s.2 id

theorem getKeypair_spec (P : View → Prop) (id : KeypairId) :
    ⦃fun w => ⌜P (view w)⌝⦄ getKeypair id
    ⦃⇓? k w => ⌜P (view w) ∧ keyAt (view w) id = some k⌝⦄ := by
  mvcgen [getKeypair, getDev, getK, invariant]
  all_goals simp_all [keyAt, view]

theorem setKeypair_spec (P : View → Prop) (stable : Stable P) (id : KeypairId) (k : Keypair) :
    ⦃fun w => ⌜P (view w) ∧ (k.receiving.isValid = true → ∃ old,
      keyAt (view w) id = some old ∧ old.receiving.isValid = true ∧ KeyLe k old)⌝⦄
      setKeypair id k ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  cases hr
  apply stable _ _ ?_ hi.1
  cases hd : w.k.wg with
  | none => simpa [view, setKeypair, modifyDev, modifyK, hd] using RetainsView.refl none
  | some d =>
    have h := retains_insert d.ifindex (fun q => d.keypairs[q]?) id k (by
      intro valid
      obtain ⟨old, hk, hv, hl⟩ := hi.2 valid
      exact ⟨old, by simpa [keyAt, view, hd] using hk, hv, hl⟩)
    simpa [view, setKeypair, modifyDev, modifyK, hd,
      Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq] using h

theorem modifyDev_spec (P : View → Prop) (f : Device → Device)
    (he : ∀ d, (f d).ifindex = d.ifindex) (hk : ∀ d, (f d).keypairs = d.keypairs) :
    ⦃fun w => ⌜P (view w)⌝⦄ modifyDev f ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [view, modifyDev, modifyK, Option.map_map, Function.comp_def, he, hk] using hp

theorem eraseKey_spec (P : View → Prop) (stable : Stable P) (id : KeypairId) :
    ⦃fun w => ⌜P (view w)⌝⦄ modifyDev (fun d => {d with keypairs := d.keypairs.erase id})
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  apply stable _ _ ?_ hp
  cases hd : w.k.wg with
  | none => simpa [view, setKeypair, modifyDev, modifyK, hd] using RetainsView.refl none
  | some d =>
    simpa [view, modifyDev, modifyK, hd, Std.TreeMap.getElem?_erase, Std.LawfulEqOrd.compare_eq_iff_eq]
      using retains_erase d.ifindex (fun q => d.keypairs[q]?) id

theorem kernel (ha : SameKernel a) : SameView view a :=
  sameView_of_sameWG (sameWGKernel_of_sameKernel ha)

theorem index (ha : SameView indexKernelView a) : SameView view a :=
  ha.of_factor (fun k => k.wg.map fun d => (d.ifindex, fun id => d.keypairs[id]?)) view
    (fun w => by cases h : w.k.wg <;> simp [view, indexKernelView, indexKernel, h])

theorem setPeer_view (id : PeerId) (p : Peer) : SameView view (setPeer id p) := by
  apply SameView.of_wp
  intro s
  simpa only [setPeer] using modifyDev_spec (fun v => v = s) (fun d => {d with peers := d.peers.insert id p}) (fun _ => rfl) (fun _ => rfl)

theorem getPeer_view (id : PeerId) : SameView view (getPeer id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getPeer, getDev, getK, invariant]

theorem keypairGet_spec (P : View → Prop) (stable : Stable P) (id : Option KeypairId) :
    ⦃fun w => ⌜P (view w)⌝⦄ keypairGet id ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  have hg := getKeypair_spec P
  have hs := setKeypair_spec P stable
  mvcgen [keypairGet, hg, hs, refcountIncNotZero, branch, branchCmp, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [KeyLe, material, WordLe, view, keyAt, Option.map_map, Function.comp_def]
  all_goals grind

theorem retains_map_insert (d : Device) (id : KeypairId) (old k : Keypair)
    (hk : d.keypairs[id]? = some old) (valid : k.receiving.isValid = true → old.receiving.isValid = true)
    (le : KeyLe k old) :
    RetainsView (some (d.ifindex, fun q => d.keypairs[q]?))
      (some (d.ifindex, fun q => (d.keypairs.insert id k)[q]?)) := by
  simpa [Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq] using
    retains_insert d.ifindex (fun q => d.keypairs[q]?) id k (fun h => ⟨old,hk,valid h,le⟩)

theorem retains_map_insert_erase (d : Device) (id : KeypairId) (k : Keypair) :
    RetainsView (some (d.ifindex, fun q => d.keypairs[q]?))
      (some (d.ifindex, fun q => ((d.keypairs.insert id k).erase id)[q]?)) := by
  simpa +contextual [Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_erase, Std.LawfulEqOrd.compare_eq_iff_eq] using
    retains_erase d.ifindex (fun q => d.keypairs[q]?) id

theorem keypairPut_spec (P : View → Prop) (stable : Stable P) (id : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜P (view w)⌝⦄ keypairPut id now ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  have action : Lifetimes.ProjectedAction view RetainsView (keypairPut id now) := by
    apply Lifetimes.ProjectedAction.of_wp
    intro s
    simp only [keypairPut, indexRemove_eq]
    have hd := fun o k => sameKernel_wp _ (indexOwner_peerDeref_sameKernel o) (fun v => v = k)
    mvcgen [hd, indexUnhash, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
      branch, branchCmp, refcountDecAndTest, unsupported, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [view]
    all_goals subst_vars
    all_goals first
      | exact RetainsView.refl _
      | exact retains_map_insert_erase _ _ _
      | apply retains_map_insert <;> first | assumption | exact fun h => h | exact KeyLe.refl _
  exact action.wp P stable

theorem modifyPeer_spec (P : View → Prop) (pid : PeerId) (f : Peer → Peer) :
    ⦃fun w => ⌜P (view w)⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  have hg := (getPeer_view pid).wp P
  have hs := fun p => (setPeer_view pid p).wp P
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  mvcgen [hg, hs]

theorem addNewKeypair_spec (P : View → Prop) (stable : Stable P) (pid kid : Nat) :
    ⦃fun w => ⌜P (view w)⌝⦄ addNewKeypair pid kid ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  have hg := (getPeer_view pid).wp P
  have hk := getKeypair_spec P
  have hm := modifyPeer_spec P
  have hp := keypairPut_spec P stable
  mvcgen [addNewKeypair, hg, hk, hm, hp, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view]

theorem handshakeZero_view (pid : PeerId) : SameView view (handshakeZero pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_view pid).wp (fun v => v = s)
  have hs := fun p => (setPeer_view pid p).wp (fun v => v = s)
  mvcgen [handshakeZero, hg, hs]

theorem indexReplace_view (pid kp : Nat) : SameView view (indexReplaceHandshake pid kp) := by
  apply SameView.of_wp
  intro s
  have hm := modifyDev_spec (fun v => v = s)
  mvcgen [indexReplaceHandshake, indexHashed, getDev, getK, invariant, branch, hm]
  all_goals simp_all [view]

theorem tail_spec (P : View → Prop) (stable : Stable P) (pid kp : Nat) :
    ⦃fun w => ⌜P (view w)⌝⦄ SessionOrigin.tail pid kp ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  have hg := (getPeer_view pid).wp P
  have hz := (handshakeZero_view pid).wp P
  have hk := addNewKeypair_spec P stable pid kp
  have hd := (kernel (indexOwner_peerDeref_sameKernel (.handshake pid))).wp P
  have hi := (indexReplace_view pid kp).wp P
  mvcgen [SessionOrigin.tail, SessionOrigin.tailWith, hg, hz, hk, hd, hi, branch, unsupported]

theorem tail_retains (pid kp : Nat) (hr : (SessionOrigin.tail pid kp).run w = .ok (x,v)) : Retains w v :=
  (hoare_iff_triple _ _ _).mpr
    (tail_spec (RetainsView (view w)) (fun _ _ a b => b.trans a) pid kp)
    w x v (RetainsView.refl _) hr

/-- Concrete field updates used by reference, replay, sending and session
initialization paths preserve receiving material; the fresh owner must still
be kept or cleared. No same-stamp-only setter principle is assumed. -/
theorem key_fields (k : Keypair) (refs nonce : Nat) (counter : ReplayCounter)
    (sending : SymmetricKey) (initiator : Bool) (remote : Nat) (valid : Bool)
    (word : Option PeerId) (hw : WordLe word k.peer) :
    KeyLe {k with refcount := refs, sendingCounter := nonce, receivingCounter := counter, sending := sending, iAmTheInitiator := initiator, remoteIndex := remote, peer := word, receiving := {k.receiving with isValid := valid}} k := ⟨rfl,hw⟩

end Leanux.Proofs.WG.Origins
