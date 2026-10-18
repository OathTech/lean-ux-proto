import Leanux.Proofs.WG.Lifetimes.ReleaseInvariant

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Packet free observes the original successful getter before release.
Stamps include the device epoch; neither helper changes that epoch. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def getTxSkbPrefix (id : SkbId) : MixedM DataPacket :=
  fun w ambient => ExceptT.mk fun h => match ((getTxSkb id).run w).run ambient with
    | .error e => (.error e, h)
    | .ok ((p, v), ambient') => (.ok ((p, v), ambient'), h ++ [.packet (.read (.inl id) (packetStamp w id))])

@[simp] theorem getTxSkbPrefix_run (id : SkbId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (getTxSkbPrefix id) w ambient h = match ((getTxSkb id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok ((p, v), ambient') => (.ok ((p, v), ambient'), h ++ [.packet (.read (.inl id) (packetStamp w id))]) := rfl

theorem getTxSkbPrefix_erases (id : SkbId) : ErasesStatePrefix (getTxSkbPrefix id) (getTxSkb id) := by
  intro w ambient h
  change (runStatePrefix (getTxSkbPrefix id) w ambient h).1 = _
  rw [getTxSkbPrefix_run]
  cases ((getTxSkb id).run w).run ambient <;> rfl

theorem mixed_getTxSkb (P : IdentityView → Prop) (id : SkbId) :
    MixedSpec P (getTxSkbPrefix id)
      (fun _ s => P s ∧ ∃ stamp, s.2.2 (.inl id) = some stamp) := by
  intro w ambient h hi
  rw [show runPrefix ((getTxSkbPrefix id).run w) ambient h =
      runStatePrefix (getTxSkbPrefix id) w ambient h from rfl, getTxSkbPrefix_run]
  cases hr : ((getTxSkb id).run w).run ambient with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, d, hd, hp⟩ := Packets.getTxSkb_current id w v p ambient ambient' hr
    have live : packetResidents v (.inl id) = some (packetStamp v id) := by
      simp [packetResidents, packetStamp, hd, hp]
    have hn := hi.1.packetRead live
    exact ⟨[.packet (.read (.inl id) (packetStamp v id))], rfl, hn.safe, hn, hi.2, _, live⟩

def packetSlotId : Packets.Slot → SkbId | .inl i => i | .inr i => i

def erasePacketDevice (slot : Packets.Slot) (d : Device) : Device := match slot with
  | .inl i => {d with txSkbs := d.txSkbs.erase i}
  | .inr i => {d with rxSkbs := d.rxSkbs.erase i}

/-- The release label is meaningful under this leaf's current-residency
contract; original free calls establish it with the preceding getter. -/
def erasePacketPrefix (slot : Packets.Slot) : MixedM Unit :=
  fun w ambient => ExceptT.mk fun h =>
    (((modifyDev (erasePacketDevice slot)).run w).run ambient,
      h ++ [.packet (.release slot (packetStamp w (packetSlotId slot)))])

@[simp] theorem erasePacketPrefix_run (slot : Packets.Slot) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (erasePacketPrefix slot) w ambient h =
      (((modifyDev (erasePacketDevice slot)).run w).run ambient,
        h ++ [.packet (.release slot (packetStamp w (packetSlotId slot)))]) := rfl

theorem erasePacketPrefix_erases (slot : Packets.Slot) :
    ErasesStatePrefix (erasePacketPrefix slot) (modifyDev (erasePacketDevice slot)) := fun _ _ _ => rfl

theorem packet_resident_stamp (hl : packetResidents w slot = some stamp) :
    stamp = packetStamp w (packetSlotId slot) := by
  cases hd : w.dev with
  | none => simp [packetResidents, hd] at hl
  | some d =>
    cases slot with
    | inl i =>
      cases hp : d.txSkbs[i]? <;> simp_all [packetResidents, packetStamp, packetSlotId]
    | inr i =>
      cases hp : d.rxSkbs[i]? <;> simp_all [packetResidents, packetStamp, packetSlotId]

theorem erasePacketPrefix_spec (slot : Packets.Slot) :
    MixedSpec (fun s => ReleaseUnique s ∧ ∃ stamp, s.2.2 slot = some stamp)
      (erasePacketPrefix slot) (fun _ => ReleaseUnique) := by
  intro w ambient h hi
  obtain ⟨stamp, hl⟩ := hi.2.2
  have hs := packet_resident_stamp hl
  subst stamp
  let v := Packets.update w (erasePacketDevice slot)
  have hp : Peers.snapshot v = Peers.snapshot w := by
    cases slot <;> simp [v, Packets.update, erasePacketDevice, Peers.snapshot, Option.bind_map, Function.comp_def]
  have hk : keypairResidents v = keypairResidents w := by
    funext j
    cases hd : w.dev <;> cases slot <;>
      simp [v, Packets.update, erasePacketDevice, keypairResidents, hd]
  have ht : packetResidents v = eraseResident (packetResidents w) slot := by
    funext j
    cases hd : w.dev with
    | none => simp [v, Packets.update, packetResidents, eraseResident, hd]
    | some d =>
      cases slot with
      | inl i =>
        cases j with
        | inl j =>
          by_cases he : j = i
          · subst j; simp [v, Packets.update, packetResidents, eraseResident, erasePacketDevice, hd]
          · simp [v, Packets.update, packetResidents, eraseResident, erasePacketDevice, hd,
              Std.TreeMap.getElem?_erase, he, Ne.symm he]
        | inr j => simp [v, Packets.update, packetResidents, eraseResident, erasePacketDevice, hd]
      | inr i =>
        cases j with
        | inl j => simp [v, Packets.update, packetResidents, eraseResident, erasePacketDevice, hd]
        | inr j =>
          by_cases he : j = i
          · subst j; simp [v, Packets.update, packetResidents, eraseResident, erasePacketDevice, hd]
          · simp [v, Packets.update, packetResidents, eraseResident, erasePacketDevice, hd,
              Std.TreeMap.getElem?_erase, he, Ne.symm he]
  have hn := ReleaseInv.packetRelease (show ReleaseInv h w from ⟨hi.1, hi.2.1⟩) hl hp hk ht
  exact ⟨[.packet (.release slot (packetStamp w (packetSlotId slot)))], rfl, hn.safe, hn⟩

def freeTxSkbPrefix (id : SkbId) : MixedM Unit := do
  let _ ← getTxSkbPrefix id
  erasePacketPrefix (.inl id)

def freeRxSkbPrefix (id : SkbId) : MixedM Unit := do
  let _ ← getRxSkbPrefix id
  erasePacketPrefix (.inr id)

theorem freeTxSkbPrefix_erases (id : SkbId) : ErasesStatePrefix (freeTxSkbPrefix id) (freeTxSkb id) := by
  have factor : freeTxSkb id =
      (getTxSkb id >>= fun _ => modifyDev (erasePacketDevice (.inl id))) := by
    funext w ambient
    change ((freeTxSkb id).run w).run ambient =
      ((getTxSkb id >>= fun _ => modifyDev (erasePacketDevice (.inl id))).run w).run ambient
    cases hd : w.dev with
    | none => simp [freeTxSkb, getTxSkb, liftSkb_run, hd,
        StateT.run_bind]
    | some d =>
      cases hp : d.txSkbs[id]? <;>
        simp [freeTxSkb, getTxSkb, liftSkb_run, SkbStore.freeTx, SkbStore.getTx,
          hd, hp, StateT.run_bind, modifyDev, invariant, AmbientM.invariant] <;> rfl
  rw [factor]
  exact erasesStatePrefix_bind (getTxSkbPrefix_erases id)
    (fun _ => erasePacketPrefix_erases (.inl id))

theorem freeRxSkbPrefix_erases (id : SkbId) : ErasesStatePrefix (freeRxSkbPrefix id) (freeRxSkb id) := by
  have factor : freeRxSkb id =
      (getRxSkb id >>= fun _ => modifyDev (erasePacketDevice (.inr id))) := by
    funext w ambient
    change ((freeRxSkb id).run w).run ambient =
      ((getRxSkb id >>= fun _ => modifyDev (erasePacketDevice (.inr id))).run w).run ambient
    cases hd : w.dev with
    | none => simp [freeRxSkb, getRxSkb, liftSkb_run, hd,
        StateT.run_bind]
    | some d =>
      cases hp : d.rxSkbs[id]? <;>
        simp [freeRxSkb, getRxSkb, liftSkb_run, SkbStore.freeRx, SkbStore.getRx,
          hd, hp, StateT.run_bind, modifyDev, invariant, AmbientM.invariant] <;> rfl
  rw [factor]
  exact erasesStatePrefix_bind (getRxSkbPrefix_erases id)
    (fun _ => erasePacketPrefix_erases (.inr id))

theorem freeTxSkbPrefix_preserves (id : SkbId) :
    StatePrefixPreserves (fun h w _ => ReleaseInv h w) LifetimeEvent.Safe (freeTxSkbPrefix id) :=
  (StatePrefixEnsures.bind (mixed_getTxSkb ReleaseUnique id)
    (fun _ => erasePacketPrefix_spec (.inl id)))

theorem freeRxSkbPrefix_preserves (id : SkbId) :
    StatePrefixPreserves (fun h w _ => ReleaseInv h w) LifetimeEvent.Safe (freeRxSkbPrefix id) :=
  (StatePrefixEnsures.bind (mixed_getRxSkb ReleaseUnique id)
    (fun _ => erasePacketPrefix_spec (.inr id)))

theorem freeTxSkbPrefix_run (id : SkbId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (freeTxSkbPrefix id) w ambient h = match ((getTxSkb id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok (_, _) => (((freeTxSkb id).run w).run ambient,
          h ++ [.packet (.read (.inl id) (packetStamp w id)),
                .packet (.release (.inl id) (packetStamp w id))]) := by
  unfold freeTxSkbPrefix
  rw [runStatePrefix_bind, getTxSkbPrefix_run]
  cases hr : ((getTxSkb id).run w).run ambient with
  | error e => rfl
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, d, hd, hp⟩ := Packets.getTxSkb_current id w v p ambient ambient' hr
    rw [Packets.freeTxSkb_run v ambient' d id p hd hp]
    simp [erasePacketPrefix_run, erasePacketDevice, modifyDev, Packets.update,
      hd, packetSlotId, List.append_assoc] <;> rfl

theorem freeRxSkbPrefix_run (id : SkbId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (freeRxSkbPrefix id) w ambient h = match ((getRxSkb id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok (_, _) => (((freeRxSkb id).run w).run ambient,
          h ++ [.packet (.read (.inr id) (packetStamp w id)),
                .packet (.release (.inr id) (packetStamp w id))]) := by
  unfold freeRxSkbPrefix
  rw [runStatePrefix_bind, getRxSkbPrefix_run]
  cases hr : ((getRxSkb id).run w).run ambient with
  | error e => rfl
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, d, hd, hp⟩ := Packets.getRxSkb_current id w v p ambient ambient' hr
    rw [Packets.freeRxSkb_run v ambient' d id p hd hp]
    simp [erasePacketPrefix_run, erasePacketDevice, modifyDev, Packets.update,
      hd, packetSlotId, List.append_assoc] <;> rfl

end Leanux.Proofs.WG.Lifetimes
