import Leanux.Proofs.WG.Lifetimes.AllocationInvariant

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! The two complete packet allocators share their frontier proof. Their only
failing action is getDev, before insertion; a successful call records the
epoch-tagged allocation and its initializing write. The all-input equation also
reproduces occupied-slot overwrites; AllocationInv excludes them from safety. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

inductive PacketAllocation where
  | tx (packet : DataPacket)
  | rx (packet : RxPacket)

namespace PacketAllocation

def slot : PacketAllocation → SkbId → Packets.Slot
  | .tx _, id => .inl id
  | .rx _, id => .inr id

def device : PacketAllocation → Device → Device
  | .tx p, d => {d with txSkbs := d.txSkbs.insert d.nextSkb p, nextSkb := d.nextSkb + 1}
  | .rx p, d => {d with rxSkbs := d.rxSkbs.insert d.nextSkb p, nextSkb := d.nextSkb + 1}

def original : PacketAllocation → M SkbId
  | .tx p => newTxSkb p
  | .rx p => newRxSkb p

theorem run (a : PacketAllocation) (w : World) :
    a.original.run w = match w.k.wg with
      | none => .error (.invariant "no WireGuard device in this trace's fixture")
      | some d => .ok (d.nextSkb, Packets.update w a.device) := by
  cases hd : w.k.wg with
  | none => cases a <;> simp [original, newTxSkb, newRxSkb, getDev, getK, hd, invariant]
  | some d => cases a with
    | tx p => simpa [Packets.update, hd, device, original] using Packets.newTxSkb_run w d p hd
    | rx p => simpa [Packets.update, hd, device, original] using Packets.newRxSkb_run w d p hd

theorem store (a : PacketAllocation) (d : Device) :
    Packets.deviceStore (a.device d) = (Packets.deviceStore d).allocate (a.slot d.nextSkb) := by
  cases a with
  | tx p => exact Packets.deviceStore_newTx d p
  | rx p => exact Packets.deviceStore_newRx d p

theorem epoch (a : PacketAllocation) (d : Device) : (a.device d).ifindex = d.ifindex := by cases a <;> rfl
theorem frontier (a : PacketAllocation) (d : Device) : (a.device d).nextSkb = d.nextSkb + 1 := by cases a <;> rfl

def observed (a : PacketAllocation) : MixedM SkbId :=
  fun w => ExceptT.mk fun h => match a.original.run w with
    | .error e => (.error e, h)
    | .ok (id, v) => (.ok (id, v), h ++
        [.packet (.allocate (a.slot id) (packetStamp w id)),
         .packet (.write (a.slot id) (packetStamp w id))])

@[simp] theorem observation (a : PacketAllocation) (w : World) (h : List LifetimeEvent) :
    runPrefix a.observed w h = match a.original.run w with
      | .error e => (.error e, h)
      | .ok (id, v) => (.ok (id, v), h ++
          [.packet (.allocate (a.slot id) (packetStamp w id)),
           .packet (.write (a.slot id) (packetStamp w id))]) := rfl

theorem erases (a : PacketAllocation) : ErasesPrefix a.observed a.original := by
  intro w h; rw [observation]; cases a.original.run w <;> rfl

end PacketAllocation

theorem packetResidents_device {w : World} {d : Device} (hd : w.k.wg = some d) (s : Packets.Slot) :
    packetResidents w s = ((Packets.deviceStore d).slots s).map (d.ifindex, ·) := by
  cases s <;> simp [packetResidents, Packets.deviceStore, hd, Option.map_map, Function.comp_def]

theorem AllocationInv.packet_allocate (hi : AllocationInv h w) (hd : w.k.wg = some d)
    (a : PacketAllocation) :
    AllocationInv (h ++ [.packet (.allocate (a.slot d.nextSkb) (d.ifindex, d.nextSkb + 1)),
      .packet (.write (a.slot d.nextSkb) (d.ifindex, d.nextSkb + 1))])
      (Packets.update w a.device) := by
  let v := Packets.update w a.device
  let events : List LifetimeEvent :=
    [.packet (.allocate (a.slot d.nextSkb) (d.ifindex, d.nextSkb + 1)),
     .packet (.write (a.slot d.nextSkb) (d.ifindex, d.nextSkb + 1))]
  have hv : v.k.wg = some (a.device d) := by simp [v, Packets.update, hd]
  have hp : Peers.snapshot v = Peers.snapshot w := by
    cases a <;> simp [v, Packets.update, PacketAllocation.device, Peers.snapshot, hd]
  have hk : keyStore v = keyStore w := by
    apply Store.ext
    · rfl
    · funext j
      cases a <;> simp [v, Packets.update, PacketAllocation.device, keyStore, keypairResidents, hd]
  have hkr : keypairResidents v = keypairResidents w := congrArg Store.slots hk
  have ht : packetResidents v = insertResident (packetResidents w) (a.slot d.nextSkb)
      (d.ifindex, d.nextSkb + 1) := by
    funext s
    rw [packetResidents_device hv, a.store d]
    by_cases he : s = a.slot d.nextSkb
    · simp [Store.allocate, insertResident, he, a.epoch, Packets.deviceStore]
    · simp [Store.allocate, insertResident, he, a.epoch, packetResidents_device hd]
  have fresh : ¬ AccessEvent.Released (h.filterMap LifetimeEvent.packet?) (d.ifindex, d.nextSkb + 1) := by
    intro hr; have := hi.packetPast d hd _ hr; omega
  have absent : ∀ s, packetResidents w s ≠ some (d.ifindex, d.nextSkb + 1) := by
    intro s hs
    rw [packetResidents_device hd] at hs
    cases hx : (Packets.deviceStore d).slots s with
    | none => simp [hx] at hs
    | some stamp =>
      simp only [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at hs
      have hb := hi.packetBounded d hd s stamp hx
      simp only [Packets.deviceStore] at hb
      omega
  have hpeer : Peers.CreationInv ((h ++ events).filterMap LifetimeEvent.peer?) v := by
    simpa [events, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?] using hi.peer.congr hp
  have hkeys : ResidentSafe ((h ++ events).filterMap LifetimeEvent.keypair?) (keypairResidents v) := by
    simpa [events, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?, hkr] using hi.release.1.keypair
  have hpacket : ResidentSafe ((h ++ events).filterMap LifetimeEvent.packet?) (packetResidents v) := by
    simpa [events, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?, ht] using
      hi.release.1.packet.allocate (i := a.slot d.nextSkb) fresh
  change AllocationInv (h ++ events) v
  refine ⟨⟨⟨hpeer.access, hkeys, hpacket⟩, ?_⟩, hpeer, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · change ResidentUnique (keypairResidents v)
      rw [hkr]; exact hi.release.2.1
    · change ResidentUnique (packetResidents v)
      rw [ht]; exact hi.release.2.2.insert absent
  · intro e he i p hl
    rw [hv] at he; cases he
    cases a <;> exact hi.peerSlots d hd i p hl
  · rw [hk]; exact hi.keyBounded
  · intro s hs
    apply hi.keyPast s
    simpa [events, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?] using hs
  · intro e he i k hl
    rw [hv] at he; cases he
    cases a <;> exact hi.keySlots d hd i k hl
  · intro e he
    rw [hv] at he; cases he
    rw [a.store]
    exact allocate_bounded _ _ (hi.packetBounded d hd)
  · intro e he
    rw [hv] at he; cases he
    rw [a.epoch]
    exact hi.epochBounded d hd
  · intro s hs
    apply hi.packetPastEpoch s
    simpa [events, List.filterMap_append, LifetimeEvent.packet?, AccessEvent.Released] using hs
  · intro e he s hs
    rw [hv] at he; cases he
    have old : AccessEvent.Released (h.filterMap LifetimeEvent.packet?) (d.ifindex, s) := by
      simpa [events, List.filterMap_append, LifetimeEvent.packet?, AccessEvent.Released, a.epoch] using hs
    rw [a.frontier]
    exact Nat.le_trans (hi.packetPast d hd s old) (Nat.le_succ _)

theorem PacketAllocation.preserves (a : PacketAllocation) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe a.observed := by
  intro w h hi
  rw [a.observation, a.run]
  cases hd : w.k.wg with
  | none => exact ⟨[], by simp, hi.safe, True.intro⟩
  | some d =>
    have hn := hi.packet_allocate hd a
    simp only [packetStamp, hd, Option.map_some, Option.getD_some]
    exact ⟨_, rfl, hn.safe, hn⟩

abbrev newTxSkbPrefix (p : DataPacket) : MixedM SkbId := (PacketAllocation.tx p).observed
abbrev newRxSkbPrefix (p : RxPacket) : MixedM SkbId := (PacketAllocation.rx p).observed

end Leanux.Proofs.WG.Lifetimes
