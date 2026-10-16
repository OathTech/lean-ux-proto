import Leanux.Proofs.WG.Lifetimes.Actions
import Leanux.Proofs.Framing.Lift

set_option pp.structureInstances false

/-! The eight original skb-store helpers, with exact successful executions.
Packet identity is its allocation number plus one in its TX or RX slot. The
shared frontier belongs to one device epoch; these helpers retain that epoch. -/
namespace Leanux.Proofs.WG.Packets
open Leanux Leanux.WG Leanux.Proofs.WG.Lifetimes Leanux.Proofs.Framing

abbrev Slot := Sum SkbId SkbId

def deviceStore (d : Device) : Store Slot :=
  ⟨d.nextSkb, fun
    | .inl i => d.txSkbs[i]?.map (fun _ => i + 1)
    | .inr i => d.rxSkbs[i]?.map (fun _ => i + 1)⟩

def snapshot (w : WGWorld) : Store Slot :=
  match w.dev with
  | none => ⟨0, fun _ => none⟩
  | some d => deviceStore d

def epoch (w : WGWorld) : Option Nat := w.dev.map (·.ifindex)

def update (w : WGWorld) (f : Device → Device) : WGWorld :=
  { w with dev := w.dev.map f }

def Inv (w : WGWorld) : Prop := Bounded (snapshot w)

def Step (w w' : WGWorld) : Prop :=
  epoch w' = epoch w ∧ Transition (snapshot w) (snapshot w')

theorem Step.refl (w : WGWorld) : Step w w := ⟨rfl, .refl _⟩

theorem Step.trans (h : Step w v) (g : Step v u) : Step w u :=
  ⟨g.1.trans h.1, h.2.trans g.2⟩

theorem newTxSkb_run (w : WGWorld) (ambient : Ambient) (d : Device) (p : DataPacket)
    (hd : w.dev = some d) :
    ((newTxSkb p).run w).run ambient = .ok ((d.nextSkb, update w fun v =>
      { v with txSkbs := v.txSkbs.insert d.nextSkb p, nextSkb := d.nextSkb + 1 }), ambient) := by
  simp [newTxSkb, liftSkb_run, SkbStore.newTx, hd, update]
  all_goals rfl

theorem getTxSkb_run (w : WGWorld) (ambient : Ambient) (d : Device) (i : SkbId) (p : DataPacket)
    (hd : w.dev = some d) (hp : d.txSkbs[i]? = some p) :
    ((getTxSkb i).run w).run ambient = .ok ((p, w), ambient) := by
  simp [getTxSkb, liftSkb_run, SkbStore.getTx, hd, hp]
  change (Except.ok ((p, {w with dev := some d}), ambient) : Except Stop _) =
    .ok ((p, w), ambient)
  rw [← hd]

theorem setTxSkb_run (w : WGWorld) (ambient : Ambient) (d : Device) (i : SkbId) (p : DataPacket)
    (f : DataPacket → DataPacket) (hd : w.dev = some d) (hp : d.txSkbs[i]? = some p) :
    ((setTxSkb i f).run w).run ambient = .ok (((), update w fun v =>
      { v with txSkbs := v.txSkbs.insert i (f p) }), ambient) := by
  simp [setTxSkb, liftSkb_run, SkbStore.setTx, SkbStore.getTx, hd, hp, update]
  all_goals rfl

theorem freeTxSkb_run (w : WGWorld) (ambient : Ambient) (d : Device) (i : SkbId) (p : DataPacket)
    (hd : w.dev = some d) (hp : d.txSkbs[i]? = some p) :
    ((freeTxSkb i).run w).run ambient = .ok (((), update w fun v =>
      { v with txSkbs := v.txSkbs.erase i }), ambient) := by
  simp [freeTxSkb, liftSkb_run, SkbStore.freeTx, SkbStore.getTx, hd, hp, update]
  all_goals rfl

theorem newRxSkb_run (w : WGWorld) (ambient : Ambient) (d : Device) (p : RxPacket)
    (hd : w.dev = some d) :
    ((newRxSkb p).run w).run ambient = .ok ((d.nextSkb, update w fun v =>
      { v with rxSkbs := v.rxSkbs.insert d.nextSkb p, nextSkb := d.nextSkb + 1 }), ambient) := by
  simp [newRxSkb, liftSkb_run, SkbStore.newRx, hd, update]
  all_goals rfl

theorem getRxSkb_run (w : WGWorld) (ambient : Ambient) (d : Device) (i : SkbId) (p : RxPacket)
    (hd : w.dev = some d) (hp : d.rxSkbs[i]? = some p) :
    ((getRxSkb i).run w).run ambient = .ok ((p, w), ambient) := by
  simp [getRxSkb, liftSkb_run, SkbStore.getRx, hd, hp]
  change (Except.ok ((p, {w with dev := some d}), ambient) : Except Stop _) =
    .ok ((p, w), ambient)
  rw [← hd]

theorem setRxSkb_run (w : WGWorld) (ambient : Ambient) (d : Device) (i : SkbId) (p : RxPacket)
    (f : RxPacket → RxPacket) (hd : w.dev = some d) (hp : d.rxSkbs[i]? = some p) :
    ((setRxSkb i f).run w).run ambient = .ok (((), update w fun v =>
      { v with rxSkbs := v.rxSkbs.insert i (f p) }), ambient) := by
  simp [setRxSkb, liftSkb_run, SkbStore.setRx, SkbStore.getRx, hd, hp, update]
  all_goals rfl

theorem freeRxSkb_run (w : WGWorld) (ambient : Ambient) (d : Device) (i : SkbId) (p : RxPacket)
    (hd : w.dev = some d) (hp : d.rxSkbs[i]? = some p) :
    ((freeRxSkb i).run w).run ambient = .ok (((), update w fun v =>
      { v with rxSkbs := v.rxSkbs.erase i }), ambient) := by
  simp [freeRxSkb, liftSkb_run, SkbStore.freeRx, SkbStore.getRx, hd, hp, update]
  all_goals rfl

theorem deviceStore_newTx (d : Device) (p : DataPacket) :
    deviceStore { d with txSkbs := d.txSkbs.insert d.nextSkb p, nextSkb := d.nextSkb + 1 } =
      (deviceStore d).allocate (.inl d.nextSkb) := by
  apply Store.ext
  · rfl
  · funext j
    cases j with
    | inl i =>
      simp only [deviceStore, Store.allocate, Std.TreeMap.getElem?_insert,
        Std.LawfulEqOrd.compare_eq_iff_eq]
      by_cases h : d.nextSkb = i <;>
        simp_all [eq_comm]
    | inr i => simp [deviceStore, Store.allocate]

theorem deviceStore_newRx (d : Device) (p : RxPacket) :
    deviceStore { d with rxSkbs := d.rxSkbs.insert d.nextSkb p, nextSkb := d.nextSkb + 1 } =
      (deviceStore d).allocate (.inr d.nextSkb) := by
  apply Store.ext
  · rfl
  · funext j
    cases j with
    | inl i => simp [deviceStore, Store.allocate]
    | inr i =>
      simp only [deviceStore, Store.allocate, Std.TreeMap.getElem?_insert,
        Std.LawfulEqOrd.compare_eq_iff_eq]
      by_cases h : d.nextSkb = i <;>
        simp_all [eq_comm]

theorem deviceStore_setTx (d : Device) (i : SkbId) (old p : DataPacket)
    (hp : d.txSkbs[i]? = some old) :
    deviceStore { d with txSkbs := d.txSkbs.insert i p } = deviceStore d := by
  apply Store.ext
  · rfl
  · funext j
    cases j with
    | inl k =>
      by_cases h : i = k <;>
        simp_all [deviceStore, Std.TreeMap.getElem?_insert]
    | inr k => rfl

theorem deviceStore_setRx (d : Device) (i : SkbId) (old p : RxPacket)
    (hp : d.rxSkbs[i]? = some old) :
    deviceStore { d with rxSkbs := d.rxSkbs.insert i p } = deviceStore d := by
  apply Store.ext
  · rfl
  · funext j
    cases j with
    | inl k => rfl
    | inr k =>
      by_cases h : i = k <;>
        simp_all [deviceStore, Std.TreeMap.getElem?_insert]

theorem deviceStore_freeTx (d : Device) (i : SkbId) :
    deviceStore { d with txSkbs := d.txSkbs.erase i } =
      (deviceStore d).put (.inl i) none := by
  apply Store.ext
  · rfl
  · funext j
    cases j with
    | inl k =>
      simp only [deviceStore, Store.put, Std.TreeMap.getElem?_erase,
        Std.LawfulEqOrd.compare_eq_iff_eq]
      by_cases h : i = k <;>
        simp [h, eq_comm]
    | inr k => simp [deviceStore, Store.put]

theorem deviceStore_freeRx (d : Device) (i : SkbId) :
    deviceStore { d with rxSkbs := d.rxSkbs.erase i } =
      (deviceStore d).put (.inr i) none := by
  apply Store.ext
  · rfl
  · funext j
    cases j with
    | inl k => simp [deviceStore, Store.put]
    | inr k =>
      simp only [deviceStore, Store.put, Std.TreeMap.getElem?_erase,
        Std.LawfulEqOrd.compare_eq_iff_eq]
      by_cases h : i = k <;>
        simp [h, eq_comm]

theorem update_contract (w : WGWorld) (d : Device) (f : Device → Device)
    (hd : w.dev = some d) (he : (f d).ifindex = d.ifindex)
    (hb : Bounded (deviceStore d) → Bounded (deviceStore (f d)))
    (ht : Transition (deviceStore d) (deviceStore (f d))) (hi : Inv w) :
    Inv (update w f) ∧ Step w (update w f) := by
  have hi' : Bounded (deviceStore d) := by simpa [Inv, snapshot, hd] using hi
  simpa [Inv, Step, snapshot, update, epoch, hd, he] using And.intro (hb hi') (And.intro he ht)

theorem newTxSkb_contract (p : DataPacket) : Action Inv Step (newTxSkb p) := by
  apply (Action.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hi hr
  cases hd : w.dev with
  | none => simp [newTxSkb, liftSkb_run, SkbStore.newTx, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    rw [newTxSkb_run w ambient d p hd] at hr
    cases hr
    apply update_contract w d _ hd rfl _ _ hi
    · rw [deviceStore_newTx]
      exact allocate_bounded _ _
    · rw [deviceStore_newTx]
      exact allocate_transition _ _

theorem getTxSkb_current (i : SkbId) (w w' : WGWorld) (p : DataPacket)
    (ambient ambient' : Ambient)
    (hr : ((getTxSkb i).run w).run ambient = .ok ((p, w'), ambient')) :
    w' = w ∧ ambient' = ambient ∧ ∃ d, w.dev = some d ∧ d.txSkbs[i]? = some p := by
  cases hd : w.dev with
  | none => simp [getTxSkb, liftSkb_run, SkbStore.getTx, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    cases hp : d.txSkbs[i]? with
    | none =>
      simp [getTxSkb, liftSkb_run, SkbStore.getTx, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some old =>
      rw [getTxSkb_run w ambient d i old hd hp] at hr
      cases hr
      exact ⟨rfl, rfl, d, rfl, hp⟩

theorem getTxSkb_contract (i : SkbId) : Action Inv Step (getTxSkb i) := by
  apply (Action.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hi hr
  rcases getTxSkb_current i w w' x ambient ambient' hr with ⟨rfl, _, _⟩
  exact ⟨hi, .refl _⟩

theorem setTxSkb_contract (i : SkbId) (f : DataPacket → DataPacket) :
    Action Inv Step (setTxSkb i f) := by
  apply (Action.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hi hr
  cases hd : w.dev with
  | none => simp [setTxSkb, SkbStore.setTx, getTxSkb, liftSkb_run, SkbStore.getTx, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    cases hp : d.txSkbs[i]? with
    | none =>
      simp [setTxSkb, SkbStore.setTx, getTxSkb, liftSkb_run, SkbStore.getTx, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some old =>
      rw [setTxSkb_run w ambient d i old f hd hp] at hr
      cases hr
      apply update_contract w d _ hd rfl _ _ hi
      · rw [deviceStore_setTx d i old (f old) hp]
        exact id
      · rw [deviceStore_setTx d i old (f old) hp]
        exact .refl _

theorem freeTxSkb_contract (i : SkbId) : Action Inv Step (freeTxSkb i) := by
  apply (Action.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hi hr
  cases hd : w.dev with
  | none => simp [freeTxSkb, SkbStore.freeTx, getTxSkb, liftSkb_run, SkbStore.getTx, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    cases hp : d.txSkbs[i]? with
    | none =>
      simp [freeTxSkb, SkbStore.freeTx, getTxSkb, liftSkb_run, SkbStore.getTx, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some old =>
      rw [freeTxSkb_run w ambient d i old hd hp] at hr
      cases hr
      apply update_contract w d _ hd rfl _ _ hi
      · rw [deviceStore_freeTx]
        exact erase_bounded _ _
      · rw [deviceStore_freeTx]
        exact erase_transition _ _

theorem newRxSkb_contract (p : RxPacket) : Action Inv Step (newRxSkb p) := by
  apply (Action.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hi hr
  cases hd : w.dev with
  | none => simp [newRxSkb, liftSkb_run, SkbStore.newRx, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    rw [newRxSkb_run w ambient d p hd] at hr
    cases hr
    apply update_contract w d _ hd rfl _ _ hi
    · rw [deviceStore_newRx]
      exact allocate_bounded _ _
    · rw [deviceStore_newRx]
      exact allocate_transition _ _

theorem getRxSkb_current (i : SkbId) (w w' : WGWorld) (p : RxPacket)
    (ambient ambient' : Ambient)
    (hr : ((getRxSkb i).run w).run ambient = .ok ((p, w'), ambient')) :
    w' = w ∧ ambient' = ambient ∧ ∃ d, w.dev = some d ∧ d.rxSkbs[i]? = some p := by
  cases hd : w.dev with
  | none => simp [getRxSkb, liftSkb_run, SkbStore.getRx, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    cases hp : d.rxSkbs[i]? with
    | none =>
      simp [getRxSkb, liftSkb_run, SkbStore.getRx, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some old =>
      rw [getRxSkb_run w ambient d i old hd hp] at hr
      cases hr
      exact ⟨rfl, rfl, d, rfl, hp⟩

theorem getRxSkb_contract (i : SkbId) : Action Inv Step (getRxSkb i) := by
  apply (Action.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hi hr
  rcases getRxSkb_current i w w' x ambient ambient' hr with ⟨rfl, _, _⟩
  exact ⟨hi, .refl _⟩

theorem setRxSkb_contract (i : SkbId) (f : RxPacket → RxPacket) :
    Action Inv Step (setRxSkb i f) := by
  apply (Action.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hi hr
  cases hd : w.dev with
  | none => simp [setRxSkb, SkbStore.setRx, getRxSkb, liftSkb_run, SkbStore.getRx, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    cases hp : d.rxSkbs[i]? with
    | none =>
      simp [setRxSkb, SkbStore.setRx, getRxSkb, liftSkb_run, SkbStore.getRx, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some old =>
      rw [setRxSkb_run w ambient d i old f hd hp] at hr
      cases hr
      apply update_contract w d _ hd rfl _ _ hi
      · rw [deviceStore_setRx d i old (f old) hp]
        exact id
      · rw [deviceStore_setRx d i old (f old) hp]
        exact .refl _

theorem freeRxSkb_contract (i : SkbId) : Action Inv Step (freeRxSkb i) := by
  apply (Action.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hi hr
  cases hd : w.dev with
  | none => simp [freeRxSkb, SkbStore.freeRx, getRxSkb, liftSkb_run, SkbStore.getRx, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    cases hp : d.rxSkbs[i]? with
    | none =>
      simp [freeRxSkb, SkbStore.freeRx, getRxSkb, liftSkb_run, SkbStore.getRx, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some old =>
      rw [freeRxSkb_run w ambient d i old hd hp] at hr
      cases hr
      apply update_contract w d _ hd rfl _ _ hi
      · rw [deviceStore_freeRx]
        exact erase_bounded _ _
      · rw [deviceStore_freeRx]
        exact erase_transition _ _

/-- Exactly the eight original packet-store primitives. This family does not
assert coverage of callers, scheduled workers or device lifecycle operations. -/
inductive Primitive : (α : Type) → WG.M α → Prop where
  | newTx (p) : Primitive SkbId (newTxSkb p)
  | getTx (i) : Primitive DataPacket (getTxSkb i)
  | setTx (i f) : Primitive Unit (setTxSkb i f)
  | freeTx (i) : Primitive Unit (freeTxSkb i)
  | newRx (p) : Primitive SkbId (newRxSkb p)
  | getRx (i) : Primitive RxPacket (getRxSkb i)
  | setRx (i f) : Primitive Unit (setRxSkb i f)
  | freeRx (i) : Primitive Unit (freeRxSkb i)

theorem primitive_contract (h : Primitive α a) : Action Inv Step a := by
  cases h with
  | newTx p => exact newTxSkb_contract p
  | getTx i => exact getTxSkb_contract i
  | setTx i f => exact setTxSkb_contract i f
  | freeTx i => exact freeTxSkb_contract i
  | newRx p => exact newRxSkb_contract p
  | getRx i => exact getRxSkb_contract i
  | setRx i f => exact setRxSkb_contract i f
  | freeRx i => exact freeRxSkb_contract i

def Sequence := Executions Primitive

theorem sequence_contract (h : Sequence w ambient w' ambient') (hi : Inv w) : Inv w' ∧ Step w w' :=
  h.contract Step.refl (fun _ _ _ => Step.trans) (fun _ h => primitive_contract h) hi

theorem allocation_slots_empty (w : WGWorld) (d : Device) (hd : w.dev = some d)
    (hi : Inv w) : d.txSkbs[d.nextSkb]? = none ∧ d.rxSkbs[d.nextSkb]? = none := by
  have hb : Bounded (deviceStore d) := by simpa [Inv, snapshot, hd] using hi
  constructor
  · cases hp : d.txSkbs[d.nextSkb]? with
    | none => rfl
    | some p =>
      have h := hb (.inl d.nextSkb) (d.nextSkb + 1) (by simp [deviceStore, hp])
      simp only [deviceStore] at h
      omega
  · cases hp : d.rxSkbs[d.nextSkb]? with
    | none => rfl
    | some p =>
      have h := hb (.inr d.nextSkb) (d.nextSkb + 1) (by simp [deviceStore, hp])
      simp only [deviceStore] at h
      omega

theorem freeTxSkb_facts (i : SkbId) (w v : WGWorld)
    (ambient ambient' : Ambient) (hi : Inv w)
    (hr : ((freeTxSkb i).run w).run ambient = .ok (((), v), ambient')) :
    Inv v ∧ i + 1 ≤ (snapshot v).frontier ∧ (snapshot v).slots (.inl i) = none := by
  have hv := ((Action.iff_run_ambient _ _ _).mp (freeTxSkb_contract i)
    w ambient () v ambient' hi hr).1
  cases hd : w.dev with
  | none => simp [freeTxSkb, SkbStore.freeTx, getTxSkb, liftSkb_run, SkbStore.getTx, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    cases hp : d.txSkbs[i]? with
    | none =>
      simp [freeTxSkb, SkbStore.freeTx, getTxSkb, liftSkb_run, SkbStore.getTx, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      have hb := hi (.inl i) (i + 1) (by simp [snapshot, deviceStore, hd, hp])
      rw [freeTxSkb_run w ambient d i p hd hp] at hr
      cases hr
      exact ⟨hv, by simpa [snapshot, update, deviceStore, hd] using hb,
        by simp [snapshot, update, deviceStore, hd]⟩

theorem freeRxSkb_facts (i : SkbId) (w v : WGWorld)
    (ambient ambient' : Ambient) (hi : Inv w)
    (hr : ((freeRxSkb i).run w).run ambient = .ok (((), v), ambient')) :
    Inv v ∧ i + 1 ≤ (snapshot v).frontier ∧ (snapshot v).slots (.inr i) = none := by
  have hv := ((Action.iff_run_ambient _ _ _).mp (freeRxSkb_contract i)
    w ambient () v ambient' hi hr).1
  cases hd : w.dev with
  | none => simp [freeRxSkb, SkbStore.freeRx, getRxSkb, liftSkb_run, SkbStore.getRx, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    cases hp : d.rxSkbs[i]? with
    | none =>
      simp [freeRxSkb, SkbStore.freeRx, getRxSkb, liftSkb_run, SkbStore.getRx, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      have hb := hi (.inr i) (i + 1) (by simp [snapshot, deviceStore, hd, hp])
      rw [freeRxSkb_run w ambient d i p hd hp] at hr
      cases hr
      exact ⟨hv, by simpa [snapshot, update, deviceStore, hd] using hb,
        by simp [snapshot, update, deviceStore, hd]⟩

theorem freedTx_unreadable (i : SkbId) (w v u out : WGWorld) (p : DataPacket)
    (ambient afterFree afterSequence afterGet : Ambient)
    (hi : Inv w) (hf : ((freeTxSkb i).run w).run ambient = .ok (((), v), afterFree))
    (hs : Sequence v afterFree u afterSequence) :
    ((getTxSkb i).run u).run afterSequence ≠ .ok ((p, out), afterGet) := by
  intro hq
  obtain ⟨hv, hb, he⟩ := freeTxSkb_facts i w v ambient afterFree hi hf
  obtain ⟨_, _, d, hd, hp⟩ := getTxSkb_current i u out p afterSequence afterGet hq
  have hl : (snapshot u).slots (.inl i) = some (i + 1) := by
    simp [snapshot, deviceStore, hd, hp]
  have hfresh := (sequence_contract hs hv).2.2.empty_fresh he hl
  exact Nat.not_lt_of_ge hb hfresh

theorem freedRx_unreadable (i : SkbId) (w v u out : WGWorld) (p : RxPacket)
    (ambient afterFree afterSequence afterGet : Ambient)
    (hi : Inv w) (hf : ((freeRxSkb i).run w).run ambient = .ok (((), v), afterFree))
    (hs : Sequence v afterFree u afterSequence) :
    ((getRxSkb i).run u).run afterSequence ≠ .ok ((p, out), afterGet) := by
  intro hq
  obtain ⟨hv, hb, he⟩ := freeRxSkb_facts i w v ambient afterFree hi hf
  obtain ⟨_, _, d, hd, hp⟩ := getRxSkb_current i u out p afterSequence afterGet hq
  have hl : (snapshot u).slots (.inr i) = some (i + 1) := by
    simp [snapshot, deviceStore, hd, hp]
  have hfresh := (sequence_contract hs hv).2.2.empty_fresh he hl
  exact Nat.not_lt_of_ge hb hfresh

end Leanux.Proofs.WG.Packets
