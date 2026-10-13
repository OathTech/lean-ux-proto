import Leanux.Proofs.WG.Lifetimes.ReleaseInvariant

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Packet free observes the original successful getter before release.
Stamps include the device epoch; neither helper changes that epoch. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def getTxSkbPrefix (id : SkbId) : MixedM DataPacket :=
  fun w => ExceptT.mk fun h => match (getTxSkb id).run w with
    | .error e => (.error e, h)
    | .ok (p, v) => (.ok (p, v), h ++ [.packet (.read (.inl id) (packetStamp w id))])

@[simp] theorem getTxSkbPrefix_run (id : SkbId) (w : World) (h : List LifetimeEvent) :
    runPrefix (getTxSkbPrefix id) w h = match (getTxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (p, v) => (.ok (p, v), h ++ [.packet (.read (.inl id) (packetStamp w id))]) := rfl

theorem getTxSkbPrefix_erases (id : SkbId) : ErasesPrefix (getTxSkbPrefix id) (getTxSkb id) := by
  intro w h; rw [getTxSkbPrefix_run]; cases (getTxSkb id).run w <;> rfl

theorem mixed_getTxSkb (P : IdentityView → Prop) (id : SkbId) :
    MixedSpec P (getTxSkbPrefix id)
      (fun _ s => P s ∧ ∃ stamp, s.2.2 (.inl id) = some stamp) := by
  intro w h hi
  rw [getTxSkbPrefix_run]
  cases hr : (getTxSkb id).run w with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨p, v⟩
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getTxSkb_current id w v p hr
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
  fun w => ExceptT.mk fun h =>
    ((modifyDev (erasePacketDevice slot)).run w,
      h ++ [.packet (.release slot (packetStamp w (packetSlotId slot)))])

@[simp] theorem erasePacketPrefix_run (slot : Packets.Slot) (w : World) (h : List LifetimeEvent) :
    runPrefix (erasePacketPrefix slot) w h =
      ((modifyDev (erasePacketDevice slot)).run w,
        h ++ [.packet (.release slot (packetStamp w (packetSlotId slot)))]) := rfl

theorem erasePacketPrefix_erases (slot : Packets.Slot) :
    ErasesPrefix (erasePacketPrefix slot) (modifyDev (erasePacketDevice slot)) := fun _ _ => rfl

theorem packet_resident_stamp (hl : packetResidents w slot = some stamp) :
    stamp = packetStamp w (packetSlotId slot) := by
  cases hd : w.k.wg with
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
  intro w h hi
  obtain ⟨stamp, hl⟩ := hi.2.2
  have hs := packet_resident_stamp hl
  subst stamp
  let v := Packets.update w (erasePacketDevice slot)
  have hp : Peers.snapshot v = Peers.snapshot w := by
    cases slot <;> simp [v, Packets.update, erasePacketDevice, Peers.snapshot, Option.bind_map, Function.comp_def]
  have hk : keypairResidents v = keypairResidents w := by
    funext j
    cases hd : w.k.wg <;> cases slot <;>
      simp [v, Packets.update, erasePacketDevice, keypairResidents, hd]
  have ht : packetResidents v = eraseResident (packetResidents w) slot := by
    funext j
    cases hd : w.k.wg with
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

theorem freeTxSkbPrefix_erases (id : SkbId) : ErasesPrefix (freeTxSkbPrefix id) (freeTxSkb id) :=
  erasesPrefix_bind (getTxSkbPrefix_erases id) (fun _ => erasePacketPrefix_erases (.inl id))

theorem freeRxSkbPrefix_erases (id : SkbId) : ErasesPrefix (freeRxSkbPrefix id) (freeRxSkb id) :=
  erasesPrefix_bind (getRxSkbPrefix_erases id) (fun _ => erasePacketPrefix_erases (.inr id))

theorem freeTxSkbPrefix_preserves (id : SkbId) :
    PrefixPreserves ReleaseInv LifetimeEvent.Safe (freeTxSkbPrefix id) :=
  (PrefixEnsures.bind (mixed_getTxSkb ReleaseUnique id)
    (fun _ => erasePacketPrefix_spec (.inl id))).preserves

theorem freeRxSkbPrefix_preserves (id : SkbId) :
    PrefixPreserves ReleaseInv LifetimeEvent.Safe (freeRxSkbPrefix id) :=
  (PrefixEnsures.bind (mixed_getRxSkb ReleaseUnique id)
    (fun _ => erasePacketPrefix_spec (.inr id))).preserves

theorem freeTxSkbPrefix_run (id : SkbId) (w : World) (h : List LifetimeEvent) :
    runPrefix (freeTxSkbPrefix id) w h = match (getTxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((freeTxSkb id).run w,
          h ++ [.packet (.read (.inl id) (packetStamp w id)),
                .packet (.release (.inl id) (packetStamp w id))]) := by
  unfold freeTxSkbPrefix
  rw [runPrefix_bind, getTxSkbPrefix_run]
  cases hr : (getTxSkb id).run w with
  | error e => rfl
  | ok out =>
    rcases out with ⟨p, v⟩
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getTxSkb_current id w v p hr
    simp [erasePacketPrefix_run, freeTxSkb, StateT.run_bind, hr, packetSlotId,
      List.append_assoc] <;> rfl

theorem freeRxSkbPrefix_run (id : SkbId) (w : World) (h : List LifetimeEvent) :
    runPrefix (freeRxSkbPrefix id) w h = match (getRxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((freeRxSkb id).run w,
          h ++ [.packet (.read (.inr id) (packetStamp w id)),
                .packet (.release (.inr id) (packetStamp w id))]) := by
  unfold freeRxSkbPrefix
  rw [runPrefix_bind, getRxSkbPrefix_run]
  cases hr : (getRxSkb id).run w with
  | error e => rfl
  | ok out =>
    rcases out with ⟨p, v⟩
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getRxSkb_current id w v p hr
    simp [erasePacketPrefix_run, freeRxSkb, StateT.run_bind, hr, packetSlotId,
      List.append_assoc] <;> rfl

end Leanux.Proofs.WG.Lifetimes
