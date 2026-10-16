import Leanux.Proofs.WG.Lifetimes.MaintenanceCalls

/-! TX setters observe their actual getter before the write. Packet stamps
are fixed by device epoch and slot; payload updates preserve that identity. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def writeTxSkbPrefix (id : SkbId) (p : DataPacket) : MixedM Unit :=
  fun w ambient => ExceptT.mk fun h =>
    (((modifyDev fun d => { d with txSkbs := d.txSkbs.insert id p }).run w).run ambient,
      if w.dev.isSome then h ++ [.packet (.write (.inl id) (packetStamp w id))] else h)

def setTxSkbPrefix (id : SkbId) (f : DataPacket → DataPacket) : MixedM Unit := do
  let p ← getTxSkbPrefix id
  writeTxSkbPrefix id (f p)


theorem writeTxSkbPrefix_erases (id : SkbId) (p : DataPacket) :
    ErasesStatePrefix (writeTxSkbPrefix id p)
      (modifyDev fun d => { d with txSkbs := d.txSkbs.insert id p }) := fun _ _ _ => rfl

theorem setTxSkbPrefix_erases (id : SkbId) (f : DataPacket → DataPacket) :
    ErasesStatePrefix (setTxSkbPrefix id f) (setTxSkb id f) := by
  have factor : setTxSkb id f = (do
      let p ← getTxSkb id
      modifyDev fun d => {d with txSkbs := d.txSkbs.insert id (f p)}) := by
    funext w ambient
    change ((setTxSkb id f).run w).run ambient =
      ((getTxSkb id >>= fun p => modifyDev fun d => {d with txSkbs := d.txSkbs.insert id (f p)}).run w).run ambient
    cases hd : w.dev with
    | none => simp [setTxSkb, getTxSkb, StateT.run_bind, liftSkb_run, hd, invariant, AmbientM.invariant]
    | some d =>
      cases hp : d.txSkbs[id]? <;>
        simp [setTxSkb, getTxSkb, StateT.run_bind, liftSkb_run, SkbStore.setTx, SkbStore.getTx,
          hd, hp, modifyDev, invariant, AmbientM.invariant] <;> rfl
  rw [factor]
  exact erasesStatePrefix_bind (getTxSkbPrefix_erases id)
    (fun p => writeTxSkbPrefix_erases id (f p))

@[simp] theorem writeTxSkbPrefix_run (id : SkbId) (p : DataPacket) (w : WGWorld)
    (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (writeTxSkbPrefix id p) w ambient h =
      (((modifyDev fun d => { d with txSkbs := d.txSkbs.insert id p }).run w).run ambient,
        if w.dev.isSome then h ++ [.packet (.write (.inl id) (packetStamp w id))] else h) := rfl

theorem setTxSkbPrefix_run (id : SkbId) (f : DataPacket → DataPacket)
    (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (setTxSkbPrefix id f) w ambient h = match ((getTxSkb id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok _ => (((setTxSkb id f).run w).run ambient,
          h ++ [.packet (.read (.inl id) (packetStamp w id)),
                .packet (.write (.inl id) (packetStamp w id))]) := by
  unfold setTxSkbPrefix
  rw [runStatePrefix_bind, getTxSkbPrefix_run]
  cases hr : ((getTxSkb id).run w).run ambient with
  | error e => rfl
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, d, hd, hp⟩ := Packets.getTxSkb_current id w v p ambient ambient' hr
    simp only [writeTxSkbPrefix_run, hd, Option.isSome_some, ↓reduceIte]
    rw [Packets.setTxSkb_run v ambient' d id p f hd hp]
    simp [modifyDev, Packets.update, hd, List.append_assoc] <;> rfl

theorem setTxSkb_identity (id : SkbId) (f : DataPacket → DataPacket) :
    SameView identityView (setTxSkb id f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  cases hd : w.dev with
  | none => simp [setTxSkb, liftSkb_run, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    cases hp : d.txSkbs[id]? with
    | none =>
      simp [setTxSkb, liftSkb_run, SkbStore.setTx, SkbStore.getTx,
        hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      rw [Packets.setTxSkb_run w ambient d id p f hd hp] at hr
      cases hr
      apply Prod.ext
      · simp [identityView, Peers.snapshot, Packets.update, hd]
      · apply Prod.ext
        · unfold identityView keypairResidents
          simp [Packets.update, hd]
        · funext slot
          cases slot with
          | inr j => simp [identityView, packetResidents, Packets.update, hd]
          | inl j =>
            by_cases hj : id = j
            · subst j
              simp [identityView, packetResidents, Packets.update, hd, hp]
            · simp [identityView, packetResidents, Packets.update, hd,
                Std.TreeMap.getElem?_insert, hj]

theorem mixed_setTxSkb (P : IdentityView → Prop) (id : SkbId) (f : DataPacket → DataPacket) :
    MixedSpec P (setTxSkbPrefix id f) (fun _ => P) := by
  intro w ambient h hi
  change ∃ suffix, _ ∧ _ ∧ _
  rw [show runPrefix ((setTxSkbPrefix id f).run w) ambient h =
    runStatePrefix (setTxSkbPrefix id f) w ambient h from rfl, setTxSkbPrefix_run]
  cases hr : ((getTxSkb id).run w).run ambient with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, d, hd, hp⟩ := Packets.getTxSkb_current id w v p ambient ambient' hr
    have live : packetResidents v (.inl id) = some (packetStamp v id) := by
      simp [packetResidents, packetStamp, hd, hp]
    have hn := (hi.1.packetRead live).packetWrite live
    have hs : ((setTxSkb id f).run v).run ambient' =
        .ok (((), Packets.update v fun d =>
          {d with txSkbs := d.txSkbs.insert id (f p)}), ambient') :=
      Packets.setTxSkb_run v ambient' d id p f hd hp
    rw [hs]
    have he := (ProjectedAction.iff_run_ambient _ _ _).mp
      (setTxSkb_identity id f) v ambient' () _ ambient' hs
    refine ⟨[.packet (.read (.inl id) (packetStamp v id)),
      .packet (.write (.inl id) (packetStamp v id))], rfl, ?_, ?_, he ▸ hi.2⟩
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn.safe
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn.congr he

theorem setTxSkb_metadata (i : SkbId) (f : DataPacket → DataPacket) :
    SameView allocationMetadata (setTxSkb i f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  cases hd : w.dev with
  | none => simp [setTxSkb, liftSkb_run, hd, invariant, AmbientM.invariant] at hr
  | some d =>
    cases hp : d.txSkbs[i]? with
    | none =>
      simp [setTxSkb, liftSkb_run, SkbStore.setTx, SkbStore.getTx,
        hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      rw [Packets.setTxSkb_run w ambient d i p f hd hp] at hr
      cases hr
      simp [allocationMetadata, deviceAllocationMetadata, Packets.update, hd]

theorem getTxSkbPrefix_allocation (P : IdentityView → Prop) (id : SkbId) :
    AmbientSpec AllocationInv P (getTxSkbPrefix id) (fun _ => P) := by
  apply allocation_state_access (releaseFromMixedState
    (mixed_state_forget (mixed_getTxSkb (fun s => ReleaseUnique s ∧ P s) id) (fun _ _ hi => hi.1)))
    (getTxSkbPrefix_erases id)
  · intro w ambient p v ambient' _ hr
    rw [(Packets.getTxSkb_current id w v p ambient ambient' hr).1]
  all_goals
    intro w ambient h s
    rw [getTxSkbPrefix_run]
    cases ((getTxSkb id).run w).run ambient <;>
      simp [List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
        LifetimeEvent.packet?, AccessEvent.Released]

theorem setTxSkbPrefix_allocation (P : IdentityView → Prop) (id : SkbId) (f : DataPacket → DataPacket) :
    AmbientSpec AllocationInv P (setTxSkbPrefix id f) (fun _ => P) := by
  apply allocation_state_access (releaseFromMixedState (mixed_setTxSkb (fun s => ReleaseUnique s ∧ P s) id f))
    (setTxSkbPrefix_erases id f)
  · intro w ambient x v ambient' _ hr
    exact Prod.ext ((ProjectedAction.iff_run_ambient _ _ _).mp (setTxSkb_identity id f) w ambient x v ambient' hr) ((ProjectedAction.iff_run_ambient _ _ _).mp (setTxSkb_metadata id f) w ambient x v ambient' hr)
  all_goals
    intro w ambient h s
    rw [setTxSkbPrefix_run]
    cases ((getTxSkb id).run w).run ambient <;>
      simp [List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
        LifetimeEvent.packet?, AccessEvent.Released]

end Leanux.Proofs.WG.Lifetimes
