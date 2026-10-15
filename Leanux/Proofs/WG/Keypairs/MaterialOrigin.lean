import Leanux.Proofs.WG.Lifetimes.Session
import Leanux.Proofs.Logged.Capture
import Leanux.Proofs.WG.KeyTimes.Receive

/-! Local material/frontier rules and a receipt journal. Validity records exact
successful original runs, independently of later residency or reference credit.
The lifetime projection uses the existing allocation invariant; original
erasure and receipt truth do not require it. -/
namespace Leanux.Proofs.WG.MaterialOrigin
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

structure Material where
  stamp : Nat
  key : List UInt8
  birthdate : Int64
  deriving DecidableEq

def material (k : Keypair) : Material :=
  ⟨k.internalId, k.receiving.key, k.receiving.birthdate⟩

theorem material_fields (k : Keypair) (refs nonce : Nat) (counter : ReplayCounter)
    (word : Option PeerId) (valid : Bool) :
    material {k with refcount := refs, sendingCounter := nonce, receivingCounter := counter, peer := word, receiving := {k.receiving with isValid := valid}} = material k := rfl

/-- The device update advances the slot frontier and installs the next global
stamp with invalid zero material. The complete World/counter update is the
existing keypairCreateCore_run equation.
Old slots below the entry frontier cannot be reused by this allocation. -/
theorem allocation_fields (w : World) (d : Device) (word : Option PeerId)
    (id : KeypairId) (below : id < d.nextKeypairId) :
    (keyAllocationDevice d (w.k.keypairCounter + 1) word).nextKeypairId = d.nextKeypairId + 1 ∧
    (keyAllocationDevice d (w.k.keypairCounter + 1) word).ifindex = d.ifindex ∧
    (keyAllocationDevice d (w.k.keypairCounter + 1) word).keypairs[d.nextKeypairId]? =
      some {internalId := w.k.keypairCounter + 1, peer := word} ∧
    (keyAllocationDevice d (w.k.keypairCounter + 1) word).keypairs[id]? = d.keypairs[id]? := by
  simp [keyAllocationDevice, Std.TreeMap.getElem?_insert, Nat.ne_of_lt below, Ne.symm (Nat.ne_of_lt below)]

/-- The remaining concrete session/sending setters also retain receiving
material. This is a field rule, not a universal contract for arbitrary setters. -/
theorem material_session_fields (k : Keypair) (initiator : Bool) (remoteIndex : Nat)
    (sending : SymmetricKey) :
    material {k with iAmTheInitiator := initiator, remoteIndex, sending} = material k := rfl

theorem allocation_fresh (w : World) (h : List LifetimeEvent) (d : Device)
    (hi : AllocationInv h w) (hd : w.k.wg = some d) :
    d.keypairs[d.nextKeypairId]? = none := hi.key_vacant hd

theorem initial_material (stamp : Nat) (word : Option PeerId) :
    material ({internalId := stamp, peer := word} : Keypair) =
      ⟨stamp, List.replicate 32 0, 0⟩ ∧
    ({internalId := stamp, peer := word} : Keypair).receiving.isValid = false := ⟨rfl, rfl⟩

inductive Event (Receipt : Type) where
  | life : LifetimeEvent → Event Receipt
  | receipt : Receipt → Event Receipt

def life? : Event R → Option LifetimeEvent
  | .life e => some e | .receipt _ => none

def Valid (valid : R → Prop) (h : List (Event R)) : Prop :=
  ∀ e ∈ h, match e with | .life _ => True | .receipt r => valid r

def access (a : MixedM α) : PrefixM (Event R) α := focusPrefix Event.life life? a

theorem access_erases (ha : ErasesPrefix a original) :
    ErasesPrefix (access (R := R) a) original := focusPrefix_erases _ _ ha

theorem access_projects (ha : PrefixPreserves AllocationInv LifetimeEvent.Safe a) :
    ProjectsUnder AllocationInv life? (access (R := R) a) a :=
  ha.projects_focus Event.life life? (fun _ => rfl)

theorem access_valid (a : MixedM α) (valid : R → Prop) :
    PrefixPreserves (fun h _ => Valid valid h) (Valid valid) (access a) := by
  intro w h hi
  refine ⟨_, rfl, ?_, ?_⟩
  · intro e he
    simp only [access, focusPrefix, runPrefix] at he
    rcases List.mem_append.mp he with he | he
    · exact hi e he
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
      trivial
  · cases hr : (runPrefix (access a) w h).1 with
    | error e => trivial
    | ok out =>
      intro e he
      simp only [access, focusPrefix, runPrefix] at he
      rcases List.mem_append.mp he with he | he
      · exact hi e he
      · obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
        trivial

theorem receipt_erases {R α : Type} {a : PrefixM (Event R) α} {original : M α} (ha : ErasesPrefix a original) (f : RunWitness α → R) :
    ErasesPrefix (receiptObserved a (Event.receipt ∘ f)) original := by
  intro w h
  rw [runPrefix_receiptObserved]
  have he := ha w h
  cases hr : runPrefix a w h with
  | mk out t => cases out <;> simpa [hr] using he

theorem receipt_valid {R α : Type} {a : PrefixM (Event R) α} {original : M α} {valid : R → Prop} (ha : ErasesPrefix a original)
    (hp : PrefixPreserves (fun h _ => Valid valid h) (Valid valid) a)
    (f : RunWitness α → R) (hf : ∀ r, r.Valid original → valid (f r)) :
    PrefixPreserves (fun h _ => Valid valid h) (Valid valid)
      (receiptObserved a (Event.receipt ∘ f)) := by
  intro w h hi
  obtain ⟨s, hs, hv, _⟩ := hp w h hi
  rw [runPrefix_receiptObserved]
  cases hr : runPrefix a w h with
  | mk out t =>
    simp only [hr] at hs hv
    cases out with
    | error e => exact ⟨s, hs, hv, trivial⟩
    | ok out =>
      rcases out with ⟨x, v⟩
      have hv' : Valid valid (t ++ [Event.receipt (f ⟨x, w, v⟩)]) := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hv e he
        · simp only [List.mem_singleton] at he
          subst e
          exact hf _ ((ha w h).symm.trans (congrArg Prod.fst hr))
      exact ⟨s ++ [Event.receipt (f ⟨x, w, v⟩)], by simp [hs, List.append_assoc], hv', hv'⟩

theorem valid_lift (valid : R → Prop) (a : M α) :
    PrefixPreserves (fun h _ => Valid valid h) (Valid valid) (liftPrefix a) := by
  intro w h hi
  refine ⟨[], by simp, hi, ?_⟩
  cases hr : a.run w with
  | error e => simp [hr]
  | ok out => simpa [hr] using hi

theorem valid_pure (valid : R → Prop) (x : α) :
    PrefixPreserves (fun h _ => Valid valid h) (Valid valid) (pure x) := by
  intro w h hi
  exact ⟨[], by simp, hi, hi⟩

/-- Exact successful bind inversion; it does not provide a World for a Stop. -/
theorem bind_ok (a : M α) (f : α → M β) (w v : World) (y : β) :
    (a >>= f).run w = .ok (y, v) ↔
      ∃ x u, a.run w = .ok (x, u) ∧ (f x).run u = .ok (y, v) := by
  simp only [StateT.run_bind]
  cases hr : a.run w with
  | error e => simp
  | ok out =>
    rcases out with ⟨x, u⟩
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro h; exact ⟨x, u, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨z, t, ⟨rfl, rfl⟩, h⟩; exact h

/-- The exact birthdate and KDF calls, followed by the actual stored record.
The original getter links the material's stamp and nullable word to its input;
no assumption that the record survives later rotation is made. -/
def Derivation (kp : KeypairId) (initiator : Bool) (ck : List UInt8) (w v : World) : Prop :=
  ∃ born a outs b first c second d key e,
    (hiddenClock64 .deriveKeysBirthdate).run w = .ok (born, a) ∧
    (kdf true false ck []).run a = .ok (outs, b) ∧
    (kdfOut outs 0).run b = .ok (first, c) ∧
    (kdfOut outs 1).run c = .ok (second, d) ∧
    (getKeypair kp).run d = .ok (key, e) ∧
    v = CounterWindow.store e kp
      (if initiator then {key with sending := {key := first, birthdate := born, isValid := true}, receiving := {key := second, birthdate := born, isValid := true}}
       else {key with receiving := {key := first, birthdate := born, isValid := true}, sending := {key := second, birthdate := born, isValid := true}})

theorem deriveKeys_execution (kp : KeypairId) (initiator : Bool) (ck : List UInt8)
    (w v : World) (hr : (deriveKeys kp initiator ck).run w = .ok ((), v)) :
    Derivation kp initiator ck w v := by
  unfold deriveKeys at hr
  simp only [bind_ok] at hr
  obtain ⟨born, a, hc, outs, b, hk, first, c, hf, second, d, hs, key, e, hg, he⟩ := hr
  refine ⟨born, a, outs, b, first, c, second, d, key, e, hc, hk, hf, hs, hg, ?_⟩
  simpa only [CounterWindow.setKeypair_run, Except.ok.injEq, Prod.mk.injEq, true_and] using he.symm

/-- Receiving material is resident at the derivation cut itself. Its identity
and nullable owner are those of the actual getter; later session cleanup may
remove it. Both selected KDF outputs and the exact birthdate call are retained
by Derivation, rather than inferred from an endpoint snapshot. -/
theorem derivation_material (kp : KeypairId) (initiator : Bool) (ck : List UInt8)
    (w v : World) (hd : Derivation kp initiator ck w v) :
    ∃ (d : Device) (key : Keypair) (born : Int64) (first second : List UInt8),
      v.k.wg = some d ∧
      d.keypairs[kp]? = some
        (if initiator then {key with sending := {key := first, birthdate := born, isValid := true}, receiving := {key := second, birthdate := born, isValid := true}}
         else {key with receiving := {key := first, birthdate := born, isValid := true}, sending := {key := second, birthdate := born, isValid := true}}) := by
  obtain ⟨born, a, outs, b, first, c, second, d, key, e, _, _, _, _, hg, rfl⟩ := hd
  obtain ⟨rfl, dev, hdev, _⟩ := KeyTimes.getKeypair_return kp d e key hg
  let updated : Keypair := if initiator then
    {key with sending := {key := first, birthdate := born, isValid := true}, receiving := {key := second, birthdate := born, isValid := true}}
    else {key with receiving := {key := first, birthdate := born, isValid := true}, sending := {key := second, birthdate := born, isValid := true}}
  refine ⟨{dev with keypairs := dev.keypairs.insert kp updated}, key, born, first, second, ?_, ?_⟩
  · simp [CounterWindow.store, hdev, updated]
  · simp [updated]

end Leanux.Proofs.WG.MaterialOrigin
