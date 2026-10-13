import Leanux.Proofs.WG.Lifetimes.MaintenanceCalls

/-! TX setters observe their actual getter before the write. Packet stamps
are fixed by device epoch and slot; payload updates preserve that identity. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def writeTxSkbPrefix (id : SkbId) (p : DataPacket) : MixedM Unit :=
  fun w => ExceptT.mk fun h =>
    ((modifyDev fun d => { d with txSkbs := d.txSkbs.insert id p }).run w,
      if w.k.wg.isSome then h ++ [.packet (.write (.inl id) (packetStamp w id))] else h)

def setTxSkbPrefix (id : SkbId) (f : DataPacket → DataPacket) : MixedM Unit := do
  let p ← getTxSkbPrefix id
  writeTxSkbPrefix id (f p)


theorem writeTxSkbPrefix_erases (id : SkbId) (p : DataPacket) :
    ErasesPrefix (writeTxSkbPrefix id p)
      (modifyDev fun d => { d with txSkbs := d.txSkbs.insert id p }) := fun _ _ => rfl

theorem setTxSkbPrefix_erases (id : SkbId) (f : DataPacket → DataPacket) :
    ErasesPrefix (setTxSkbPrefix id f) (setTxSkb id f) :=
  erasesPrefix_bind (getTxSkbPrefix_erases id) (fun p => writeTxSkbPrefix_erases id (f p))


@[simp] theorem writeTxSkbPrefix_run (id : SkbId) (p : DataPacket) (w : World) (h : List LifetimeEvent) :
    runPrefix (writeTxSkbPrefix id p) w h =
      ((modifyDev fun d => { d with txSkbs := d.txSkbs.insert id p }).run w,
        if w.k.wg.isSome then h ++ [.packet (.write (.inl id) (packetStamp w id))] else h) := rfl

theorem setTxSkbPrefix_run (id : SkbId) (f : DataPacket → DataPacket)
    (w : World) (h : List LifetimeEvent) :
    runPrefix (setTxSkbPrefix id f) w h = match (getTxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((setTxSkb id f).run w,
          h ++ [.packet (.read (.inl id) (packetStamp w id)),
                .packet (.write (.inl id) (packetStamp w id))]) := by
  unfold setTxSkbPrefix
  rw [runPrefix_bind, getTxSkbPrefix_run]
  cases hr : (getTxSkb id).run w with
  | error e => rfl
  | ok out =>
    rcases out with ⟨p, v⟩
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getTxSkb_current id w v p hr
    simp only [writeTxSkbPrefix_run, hd, Option.isSome_some, ↓reduceIte]
    simp [setTxSkb, StateT.run_bind, hr, List.append_assoc]


theorem setTxSkb_identity (id : SkbId) (f : DataPacket → DataPacket) :
    SameView identityView (setTxSkb id f) := by
  intro w x v hr
  cases x
  cases hd : w.k.wg with
  | none => simp [setTxSkb, getTxSkb, getDev, getK, hd, invariant] at hr
  | some d =>
    cases hp : d.txSkbs[id]? with
    | none => simp [setTxSkb, getTxSkb, getDev, getK, hd, hp, invariant] at hr
    | some p =>
      rw [Packets.setTxSkb_run w d id p f hd hp] at hr
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
  intro w h hi
  rw [setTxSkbPrefix_run]
  cases hr : (getTxSkb id).run w with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨p, v⟩
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getTxSkb_current id w v p hr
    have live : packetResidents v (.inl id) = some (packetStamp v id) := by
      simp [packetResidents, packetStamp, hd, hp]
    have hn := (hi.1.packetRead live).packetWrite live
    have hs : (setTxSkb id f).run v = .ok ((), Packets.update v fun d =>
        {d with txSkbs := d.txSkbs.insert id (f p)}) := Packets.setTxSkb_run v d id p f hd hp
    rw [hs]
    have he := setTxSkb_identity id f v () _ hs
    refine ⟨[.packet (.read (.inl id) (packetStamp v id)),
      .packet (.write (.inl id) (packetStamp v id))], rfl, ?_, ?_, he ▸ hi.2⟩
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn.safe
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn.congr he


theorem setTxSkb_metadata (i : SkbId) (f : DataPacket → DataPacket) :
    SameView allocationMetadata (setTxSkb i f) := by
  unfold setTxSkb
  apply SameView.bind
  · intro w p v hr
    exact congrArg allocationMetadata (Packets.getTxSkb_current i w v p hr).1
  · intro p; exact metadata_modifyDev _ (fun _ => rfl)

theorem getTxSkbPrefix_allocation (P : IdentityView → Prop) (id : SkbId) :
    AmbientSpec AllocationInv P (getTxSkbPrefix id) (fun _ => P) := by
  apply allocation_access (releaseFromMixed
    (mixed_forget (mixed_getTxSkb (fun s => ReleaseUnique s ∧ P s) id) (fun _ _ hi => hi.1)))
    (getTxSkbPrefix_erases id)
  · intro w p v _ hr
    rw [(Packets.getTxSkb_current id w v p hr).1]
  all_goals
    intro w h s
    rw [getTxSkbPrefix_run]
    cases (getTxSkb id).run w <;>
      simp [List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
        LifetimeEvent.packet?, AccessEvent.Released]

theorem setTxSkbPrefix_allocation (P : IdentityView → Prop) (id : SkbId) (f : DataPacket → DataPacket) :
    AmbientSpec AllocationInv P (setTxSkbPrefix id f) (fun _ => P) := by
  apply allocation_access (releaseFromMixed (mixed_setTxSkb (fun s => ReleaseUnique s ∧ P s) id f))
    (setTxSkbPrefix_erases id f)
  · intro w x v _ hr
    exact Prod.ext (setTxSkb_identity id f w x v hr) (setTxSkb_metadata id f w x v hr)
  all_goals
    intro w h s
    rw [setTxSkbPrefix_run]
    cases (getTxSkb id).run w <;>
      simp [List.filterMap_append, LifetimeEvent.peer?, LifetimeEvent.keypair?,
        LifetimeEvent.packet?, AccessEvent.Released]

end Leanux.Proofs.WG.Lifetimes
