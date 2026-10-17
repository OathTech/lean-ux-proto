import Leanux.Proofs.WG.Keypairs.SessionOrigin
import Leanux.Proofs.Framing.WGKernel
import Leanux.Proofs.Framing.Product

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
def view (w : WGWorld) : View := w.dev.map fun d => (d.ifindex, fun id => d.keypairs[id]?)

def KeyLe (current original : Keypair) : Prop :=
  material current = material original ∧ WordLe current.peer original.peer

def RetainsView (before after : View) : Prop :=
  ∀ epoch keys, after = some (epoch, keys) →
    ∀ id k, keys id = some k → k.receiving.isValid = true →
      ∃ oldKeys old, before = some (epoch, oldKeys) ∧ oldKeys id = some old ∧
        old.receiving.isValid = true ∧ KeyLe k old

def Retains (before after : WGWorld) : Prop := RetainsView (view before) (view after)

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

theorem Retains.refl (w : WGWorld) : Retains w w := RetainsView.refl _
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

/-- One successful original front, its full Context and both WG/Ambient
endpoints support this exact resident allocation/material and keep-or-clear word. -/
def Supported (history : List SessionOrigin.Receipt) (epoch : Nat)
    (slot : KeypairId) (key : Keypair) : Prop :=
  ∃ (pid : PeerId) (run : WGRunWitness (Option SessionOrigin.Context))
    (ctx : SessionOrigin.Context) (d : Device) (original : Keypair),
    SessionOrigin.Receipt.material pid run ∈ history ∧
    run.Valid (SessionOrigin.front pid) ∧ run.value = some ctx ∧ ctx.slot = slot ∧
    run.after.dev = some d ∧ d.ifindex = epoch ∧ d.keypairs[slot]? = some original ∧
    original.receiving.isValid = true ∧ original.peer = ctx.word ∧
    material key = material original ∧ WordLe key.peer ctx.word

def InvView (history : List SessionOrigin.Receipt) (v : View) : Prop :=
  ∀ epoch keys, v = some (epoch, keys) →
    ∀ id key, keys id = some key → key.receiving.isValid = true → Supported history epoch id key

def Inv (history : List SessionOrigin.Receipt) (w : WGWorld) : Prop := InvView history (view w)

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

theorem inv_empty_absent (hw : w.dev = none) : Inv [] w := by
  intro epoch keys h; simp [view, hw] at h

/-- Pure projection transports retain arbitrary actual state and action domains. -/
theorem sameView_of_sameWG {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => wgStoreView (project s)) a) :
    SameView (fun s => view (project s)) a :=
  ha.factor (fun v : WGStoreView => v.dev.map fun (d : Device) => (d.ifindex, fun (id : KeypairId) => d.keypairs[id]?))

/-- The partial relational contract specializes to the original product
endpoint statement and to native WG/Ambient runs via the actual run bridges. -/
theorem retains_of_sameView {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => view (project s)) a) :
    Lifetimes.ProjectedAction (fun s => view (project s)) RetainsView a := by
  intro initial
  apply hoare_consequence (ha initial) (fun _ h => h)
  intro _ s hs
  rw [hs]
  exact RetainsView.refl _

def Stable (P : View → Prop) : Prop := ∀ a b, RetainsView a b → P a → P b

theorem inv_stable (h : List SessionOrigin.Receipt) : Stable (InvView h) :=
  fun _ _ hr hi => hi.retain hr

def keyAt (v : View) (id : KeypairId) : Option Keypair := v.bind fun s => s.2 id

theorem getKeypair_spec (P : View → Prop) (id : KeypairId) :
    ⦃fun w => ⌜P (view w)⌝⦄ getKeypair id
    ⦃⇓? k w => ⌜P (view w) ∧ keyAt (view w) id = some k⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient k v ambient' hp hr
  cases hd : w.dev with
  | none =>
    simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hk : d.keypairs[id]? with
    | none =>
      simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      cases hr
    | some key =>
      simp [getKeypair, getDev, hd, hk] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨hp, by simp [keyAt, view, hd, hk]⟩

theorem setKeypair_spec (P : View → Prop) (stable : Stable P) (id : KeypairId) (k : Keypair) :
    ⦃fun w => ⌜P (view w) ∧ (k.receiving.isValid = true → ∃ old,
      keyAt (view w) id = some old ∧ old.receiving.isValid = true ∧ KeyLe k old)⌝⦄
      setKeypair id k ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  cases hr
  apply stable _ _ ?_ hi.1
  cases hd : w.dev with
  | none => simpa [view, setKeypair, modifyDev, hd] using RetainsView.refl none
  | some d =>
    have h := retains_insert d.ifindex (fun q => d.keypairs[q]?) id k (by
      intro valid
      obtain ⟨old, hk, hv, hl⟩ := hi.2 valid
      exact ⟨old, by simpa [keyAt, view, hd] using hk, hv, hl⟩)
    simpa [view, setKeypair, modifyDev, hd,
      Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq] using h

theorem modifyDev_spec (P : View → Prop) (f : Device → Device)
    (he : ∀ d, (f d).ifindex = d.ifindex) (hk : ∀ d, (f d).keypairs = d.keypairs) :
    ⦃fun w => ⌜P (view w)⌝⦄ modifyDev f ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hp hr
  cases hr
  simpa [view, modifyDev, Option.map_map, Function.comp_def, he, hk] using hp

theorem eraseKey_spec (P : View → Prop) (stable : Stable P) (id : KeypairId) :
    ⦃fun w => ⌜P (view w)⌝⦄ modifyDev (fun d => {d with keypairs := d.keypairs.erase id})
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hp hr
  cases hr
  apply stable _ _ ?_ hp
  cases hd : w.dev with
  | none => simpa [view, setKeypair, modifyDev, hd] using RetainsView.refl none
  | some d =>
    simpa [view, modifyDev, hd, Std.TreeMap.getElem?_erase, Std.LawfulEqOrd.compare_eq_iff_eq]
      using retains_erase d.ifindex (fun q => d.keypairs[q]?) id

theorem kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → World} {a : StateT S m α}
    (ha : SameView (fun s => productStoreView (project s)) a) :
    SameView (fun s => view (project s).wg) a :=
  ha.factor (fun k : ProductStore43 => k.2.2.2.dev.map fun (d : Device) =>
    (d.ifindex, fun (id : KeypairId) => d.keypairs[id]?))

/-- The old masked-index premise factors through seven WG store fields.
Only the index table is omitted; arbitrary product actions remain instances. -/
theorem index {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s =>
      {wgStoreView (project s) with dev := (project s).dev.map fun (d : Device) =>
        {d with indexTable := []}}) a) :
    SameView (fun s => view (project s)) a :=
  ha.of_factor (fun k : WGStoreView => k.dev.map fun (d : Device) =>
    (d.ifindex, fun (id : KeypairId) => d.keypairs[id]?)) (fun s => view (project s))
    (fun s => by cases h : (project s).dev <;> simp [view, h])

theorem setPeer_view (id : PeerId) (p : Peer) : SameView view (setPeer id p) := by
  apply SameView.of_wp
  intro s
  simpa only [setPeer] using modifyDev_spec (fun v => v = s) (fun d => {d with peers := d.peers.insert id p}) (fun _ => rfl) (fun _ => rfl)

theorem getPeer_view (id : PeerId) : SameView view (getPeer id) := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hp hr
  cases hd : w.dev with
  | none =>
    simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hk : d.peers[id]? with
    | none =>
      simp [getPeer, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      cases hr
    | some peer =>
      simp [getPeer, getDev, hd, hk] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hp

theorem keypairGet_spec (P : View → Prop) (stable : Stable P) (id : Option KeypairId) :
    ⦃fun w => ⌜P (view w)⌝⦄ keypairGet id ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hp hr
  cases id with
  | none =>
    simp [keypairGet, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact hp
  | some id =>
    cases hd : w.dev with
    | none =>
      simp [keypairGet, getKeypair, getDev, hd, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[id]? with
      | none =>
        simp [keypairGet, getKeypair, getDev, hd, hk, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at hr
        cases hr
      | some key =>
        simp only [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
          branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, refcountIncNotZero,
          unsupported, invariant, AmbientM.unsupported, AmbientM.invariant,
          StateT.run_bind] at hr
        simp [hd, hk] at hr
        repeat' split at hr <;> simp_all
        all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        all_goals first
          | exact hp
          | apply stable _ _ ?_ hp
            simp only [view, hd, Option.map_some]
            apply (show RetainsView (some (d.ifindex, fun q => d.keypairs[q]?))
              (some (d.ifindex, fun q => (d.keypairs.insert id {key with refcount := key.refcount + 1})[q]?)) from ?_)
            simpa [Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq] using
              (retains_insert d.ifindex (fun q => d.keypairs[q]?) id
                {key with refcount := key.refcount + 1}
                (fun valid => ⟨key, hk, valid, rfl, WordLe.refl _⟩))

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
  let Q := fun w : WGWorld => P (view w)
  have ambient {α : Type} (a : AmbientM α) (R : WGWorld → Prop) :
      Preserves R (monadLift a : WG.M α) := hoare_liftAmbient a R
  have remove (kid : KeypairId) (R : View → Prop) : Preserves (fun w => R (view w))
      (do let _ ← IndexOwner.peerDeref (.keypair kid); indexRemove (.keypair kid)) := by
    apply preserves_bind (indexOwner_peerDeref_preserves _ _)
    intro _
    rw [indexRemove_eq]
    apply hoare_liftIndex
    intro w d table hi hd
    simpa [view, hd] using hi
  cases id with
  | none =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hp hr
    simp [keypairPut, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact hp
  | some kid =>
    change Preserves Q (keypairPut (some kid) now)
    unfold keypairPut
    apply preserves_bind (ambient _ Q)
    intro null
    split
    · exact preserves_pure _
    · simp only
      apply hoare_bind _ _ (getKeypair_spec P kid)
      intro key
      let R := fun w : WGWorld => Q w ∧ keyAt (view w) kid = some key
      have unhash : Preserves R
          (do let _ ← IndexOwner.peerDeref (.keypair kid); indexRemove (.keypair kid)) :=
        remove kid (fun s => P s ∧ keyAt s kid = some key)
      let releaseEntry : WG.M Unit := do
        let _ ← IndexOwner.peerDeref (.keypair kid)
        indexRemove (.keypair kid)
      have afterRef : Hoare (do
          setKeypair kid {key with refcount := key.refcount - 1}
          if ← branch .keypairKrefPutReleased (← refcountDecAndTest key.refcount) then
            releaseEntry
            modifyDev fun d => {d with keypairs := d.keypairs.erase kid})
          R (fun _ => Q) := by
        apply hoare_bind _ _ (hoare_consequence
          (setKeypair_spec P stable kid {key with refcount := key.refcount - 1})
          (fun w h => ⟨h.1, fun valid => ⟨key, h.2, valid, rfl, WordLe.refl _⟩⟩)
          (fun _ _ h => h))
        intro _
        change Preserves Q _
        have rc : Preserves Q (refcountDecAndTest key.refcount : WG.M Bool) := by
          unfold refcountDecAndTest
          simp only [branch, branchCmp, unsupported]
          repeat' first
            | (allocation_release_lift_from AmbientM; exact ambient _ Q)
            | allocation_release_step
        apply preserves_bind rc
        intro released
        apply preserves_bind (ambient _ Q)
        intro release
        split
        · exact preserves_bind (remove kid P) (fun _ => eraseKey_spec P stable kid)
        · exact preserves_pure _
      apply hoare_bind _ _ (ambient (AmbientM.branch .keypairPutUnreferenceNow now) R)
      intro unref
      split
      · exact hoare_bind _ _ unhash (fun _ => afterRef)
      · exact afterRef

theorem modifyPeer_spec (P : View → Prop) (pid : PeerId) (f : Peer → Peer) :
    ⦃fun w => ⌜P (view w)⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  have hg := (getPeer_view pid).wp P
  have hs := fun p => (setPeer_view pid p).wp P
  change ⦃fun w => ⌜P (view w)⌝⦄ (do setPeer pid (f (← getPeer pid)))
    ⦃⇓? _ w => ⌜P (view w)⌝⦄
  exact preserves_bind hg (fun p => hs (f p))

theorem addNewKeypair_spec (P : View → Prop) (stable : Stable P) (pid kid : Nat) :
    ⦃fun w => ⌜P (view w)⌝⦄ addNewKeypair pid kid ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  let Q := fun w : WGWorld => P (view w)
  have hg : Preserves Q (getPeer pid) := (getPeer_view pid).wp P
  have hk (kid : KeypairId) : Preserves Q (getKeypair kid) :=
    hoare_consequence (getKeypair_spec P kid) (fun _ h => h) (fun _ _ h => h.1)
  have hm (pid : PeerId) (f : Peer → Peer) : Preserves Q
      ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) :=
    modifyPeer_spec P pid f
  have hp (id : Option KeypairId) (now : Bool) : Preserves Q (keypairPut id now) :=
    keypairPut_spec P stable id now
  have ambient {α : Type} (a : AmbientM α) : Preserves Q (monadLift a : WG.M α) :=
    hoare_liftAmbient a Q
  change Preserves Q (addNewKeypair pid kid)
  unfold addNewKeypair
  simp only [branch]
  repeat' first
    | (allocation_release_head getPeer; exact hg)
    | (allocation_release_head getKeypair; exact hk _)
    | (allocation_release_head keypairPut; exact hp _ _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step
  all_goals exact hm _ _

theorem handshakeZero_view (pid : PeerId) : SameView view (handshakeZero pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_view pid).wp (fun v => v = s)
  have hs := fun p => (setPeer_view pid p).wp (fun v => v = s)
  unfold handshakeZero
  exact preserves_bind hg (fun p => hs _)

theorem tail_spec (P : View → Prop) (stable : Stable P) (pid kp : Nat) :
    ⦃fun w => ⌜P (view w)⌝⦄ SessionOrigin.tail pid kp ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  have hg := (getPeer_view pid).wp P
  have hz := (handshakeZero_view pid).wp P
  have hk := addNewKeypair_spec P stable pid kp
  have hd := indexOwner_peerDeref_preserves (.handshake pid) (fun w => P (view w))
  have hi : Hoare (liftIndex (indexReplaceHandshake pid kp))
      (fun w => P (view w)) (fun _ w => P (view w)) := by
    apply hoare_liftIndex
    intro g d table hp hdev
    simpa [view, hdev] using hp
  let Q := fun w : WGWorld => P (view w)
  have ambient {α : Type} (a : AmbientM α) : Preserves Q (monadLift a : WG.M α) :=
    hoare_liftAmbient a Q
  change Preserves Q (SessionOrigin.tail pid kp)
  unfold SessionOrigin.tail SessionOrigin.tailWith
  simp only [branch, unsupported]
  repeat' first
    | (allocation_release_head getPeer; exact hg)
    | (allocation_release_head handshakeZero; exact hz)
    | (allocation_release_head addNewKeypair; exact hk)
    | (allocation_release_head IndexOwner.peerDeref; exact hd)
    | (allocation_release_head liftIndex; exact hi)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem tail_retains (pid kp : Nat) (ambient ambient' : Ambient)
    (hr : ((SessionOrigin.tail pid kp).run w).run ambient = .ok ((x, v), ambient')) :
    Retains w v :=
  (hoare_iff_run_ambient _ _ _).mp
    (tail_spec (RetainsView (view w)) (fun _ _ a b => b.trans a) pid kp)
    w ambient x v ambient' (RetainsView.refl _) hr

/-- Concrete field updates used by reference, replay, sending and session
initialization paths preserve receiving material; the fresh owner must still
be kept or cleared. No same-stamp-only setter principle is assumed. -/
theorem key_fields (k : Keypair) (refs nonce : Nat) (counter : ReplayCounter)
    (sending : SymmetricKey) (initiator : Bool) (remote : Nat) (valid : Bool)
    (word : Option PeerId) (hw : WordLe word k.peer) :
    KeyLe {k with refcount := refs, sendingCounter := nonce, receivingCounter := counter, sending := sending, iAmTheInitiator := initiator, remoteIndex := remote, peer := word, receiving := {k.receiving with isValid := valid}} k := ⟨rfl,hw⟩

end Leanux.Proofs.WG.Origins
