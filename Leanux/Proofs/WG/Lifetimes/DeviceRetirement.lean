import Leanux.Proofs.WG.Lifetimes.AllocationReleases

/-! Logical retirement at the original final device-store removal. The suffix
names every actually resident peer, keypair and packet immediately before that
mutation. It is accounting for one store drop, not simulated per-object kernel
free calls or a consequence of work queues being empty. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def deviceRetirementEvents (w : World) : List LifetimeEvent :=
  match w.k.wg with
  | none => []
  | some d =>
    d.peers.toList.map (fun (i,p) => .peer (.release i p.internalId)) ++
    d.keypairs.toList.map (fun (i,k) => .keypair (.release i k.internalId)) ++
    d.txSkbs.toList.map (fun (i,_) => .packet (.release (.inl i) (d.ifindex, i+1))) ++
    d.rxSkbs.toList.map (fun (i,_) => .packet (.release (.inr i) (d.ifindex, i+1)))

def deviceDropped (w : World) : World := {w with k := {w.k with wg := none}}

def dropDevicePrefix : MixedM Unit :=
  fun w => ExceptT.mk fun h =>
    (.ok ((), deviceDropped w), h ++ deviceRetirementEvents w)

theorem dropDevicePrefix_run (w : World) (h : List LifetimeEvent) :
    runPrefix dropDevicePrefix w h =
      (.ok ((), deviceDropped w), h ++ deviceRetirementEvents w) := rfl

theorem dropDevicePrefix_erases :
    ErasesPrefix dropDevicePrefix (modifyK fun k => {k with wg := none}) := fun _ _ => rfl

theorem deviceRetirementEvents_peer (w : World) (i stamp : Nat) :
    .peer (.release i stamp) ∈ deviceRetirementEvents w ↔
      (Peers.snapshot w).slots i = some stamp := by
  cases hd : w.k.wg with
  | none => simp [deviceRetirementEvents, Peers.snapshot, hd]
  | some d =>
    simp only [deviceRetirementEvents, hd, List.mem_append, List.mem_map,
      Peers.snapshot, Option.bind_some]
    simp only [LifetimeEvent.peer.injEq, AccessEvent.release.injEq,
      reduceCtorEq, and_false, exists_false, or_false]
    constructor
    · rintro ⟨⟨j,p⟩, hm, hj, hs⟩
      dsimp only at hj hs
      subst j
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hm]
      simpa using hs
    · intro hp
      cases hl : d.peers[i]? with
      | none => simp [hl] at hp
      | some p =>
        exact ⟨(i,p), Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hl,
          rfl, by simpa [hl] using hp⟩

theorem deviceRetirementEvents_key (w : World) (i stamp : Nat) :
    .keypair (.release i stamp) ∈ deviceRetirementEvents w ↔
      keypairResidents w i = some stamp := by
  cases hd : w.k.wg with
  | none => simp [deviceRetirementEvents, keypairResidents, hd]
  | some d =>
    simp only [deviceRetirementEvents, hd, List.mem_append, List.mem_map,
      keypairResidents, Option.bind_some]
    simp only [LifetimeEvent.keypair.injEq, AccessEvent.release.injEq,
      reduceCtorEq, and_false, exists_false, or_false, false_or]
    constructor
    · rintro ⟨⟨j,k⟩, hm, hj, hs⟩
      dsimp only at hj hs
      subst j
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hm]
      simpa using hs
    · intro hp
      cases hl : d.keypairs[i]? with
      | none => simp [hl] at hp
      | some k =>
        exact ⟨(i,k), Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hl,
          rfl, by simpa [hl] using hp⟩

theorem deviceRetirementEvents_packet (w : World) (i : Packets.Slot) (stamp : PacketStamp) :
    .packet (.release i stamp) ∈ deviceRetirementEvents w ↔
      packetResidents w i = some stamp := by
  cases hd : w.k.wg with
  | none => simp [deviceRetirementEvents, packetResidents, hd]
  | some d =>
    cases i with
    | inl i =>
      simp only [deviceRetirementEvents, hd, List.mem_append, List.mem_map,
        packetResidents, Option.bind_some]
      simp only [LifetimeEvent.packet.injEq, AccessEvent.release.injEq,
        Sum.inl.injEq, reduceCtorEq, and_false, false_and, exists_false, or_false, false_or]
      constructor
      · rintro ⟨⟨j,p⟩, hm, hj, hs⟩
        dsimp only at hj hs
        subst j
        rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hm]
        simpa using hs
      · intro hp
        cases hl : d.txSkbs[i]? with
        | none => simp [hl] at hp
        | some p => exact ⟨(i,p), Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hl,
            rfl, by simpa [hl] using hp⟩
    | inr i =>
      simp only [deviceRetirementEvents, hd, List.mem_append, List.mem_map,
        packetResidents, Option.bind_some]
      simp only [LifetimeEvent.packet.injEq, AccessEvent.release.injEq,
        Sum.inr.injEq, reduceCtorEq, and_false, false_and, exists_false, or_false, false_or]
      constructor
      · rintro ⟨⟨j,p⟩, hm, hj, hs⟩
        dsimp only at hj hs
        subst j
        rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hm]
        simpa using hs
      · intro hp
        cases hl : d.rxSkbs[i]? with
        | none => simp [hl] at hp
        | some p => exact ⟨(i,p), Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hl,
            rfl, by simpa [hl] using hp⟩

def LifetimeEvent.IsRelease : LifetimeEvent → Prop
  | .peer (.release ..) | .keypair (.release ..) | .packet (.release ..) => True
  | _ => False

theorem LifetimeEvent.Safe.append_releases (hs : LifetimeEvent.Safe h)
    (he : ∀ e ∈ es, LifetimeEvent.IsRelease e) : LifetimeEvent.Safe (h ++ es) := by
  induction es generalizing h with
  | nil => simpa using hs
  | cons e es ih =>
    have hr := he e (by simp)
    have step : LifetimeEvent.Safe (h ++ [e]) := by
      cases e with
      | peer e => cases e <;> simp only [LifetimeEvent.IsRelease] at hr
                  all_goals try contradiction
                  exact ⟨by simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?] using AccessEvent.safe_append_release hs.1,
                    by simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?, LifetimeEvent.packet?] using hs.2⟩
      | keypair e => cases e <;> simp only [LifetimeEvent.IsRelease] at hr
                     all_goals try contradiction
                     exact ⟨by simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?] using hs.1,
                       by simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?] using AccessEvent.safe_append_release hs.2.1,
                       by simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?] using hs.2.2⟩
      | packet e => cases e <;> simp only [LifetimeEvent.IsRelease] at hr
                    all_goals try contradiction
                    exact ⟨by simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?] using hs.1,
                      by simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?] using hs.2.1,
                      by simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?] using AccessEvent.safe_append_release hs.2.2⟩
    simpa [List.append_assoc] using ih step (fun x hx => he x (by simp [hx]))

theorem deviceRetirementEvents_releases (w : World) :
    ∀ e ∈ deviceRetirementEvents w, LifetimeEvent.IsRelease e := by
  intro e he
  cases hd : w.k.wg with
  | none => simp [deviceRetirementEvents, hd] at he
  | some d =>
    simp only [deviceRetirementEvents, hd, List.mem_append, List.mem_map] at he
    rcases he with ((⟨x, _, rfl⟩ | ⟨x, _, rfl⟩) | ⟨x, _, rfl⟩) | ⟨x, _, rfl⟩ <;> trivial

theorem deviceRetirementEvents_origin (w : World) (h : List LifetimeEvent) :
    ReleaseOrigin h (h ++ deviceRetirementEvents w) w := by
  constructor
  all_goals intro stamp hs
  all_goals rw [List.filterMap_append, AccessEvent.released_append] at hs
  all_goals rcases hs with old | ⟨i, hi⟩
  all_goals try exact Or.inl old
  · right; refine ⟨i, (deviceRetirementEvents_peer w i stamp).mp ?_⟩
    obtain ⟨e, he, hp⟩ := List.mem_filterMap.mp hi
    cases e <;> simp only [LifetimeEvent.peer?, Option.some.injEq, reduceCtorEq] at hp
    subst_vars; exact he
  · right; refine ⟨i, (deviceRetirementEvents_key w i stamp).mp ?_⟩
    obtain ⟨e, he, hp⟩ := List.mem_filterMap.mp hi
    cases e <;> simp only [LifetimeEvent.keypair?, Option.some.injEq, reduceCtorEq] at hp
    subst_vars; exact he
  · right; refine ⟨i, (deviceRetirementEvents_packet w i stamp).mp ?_⟩
    obtain ⟨e, he, hp⟩ := List.mem_filterMap.mp hi
    cases e <;> simp only [LifetimeEvent.packet?, Option.some.injEq, reduceCtorEq] at hp
    subst_vars; exact he

theorem AllocationInv.dropDevice (hi : AllocationInv h w) :
    AllocationInv (h ++ deviceRetirementEvents w) (deviceDropped w) := by
  have hs := hi.safe.append_releases (deviceRetirementEvents_releases w)
  have ho := deviceRetirementEvents_origin w h
  have hr : ReleaseInv (h ++ deviceRetirementEvents w) (deviceDropped w) := by
    refine ⟨⟨⟨hs.1, ?_, ?_⟩, ⟨hs.2.1, ?_⟩, ⟨hs.2.2, ?_⟩⟩, ?_, ?_⟩
    all_goals simp [deviceDropped, Peers.snapshot, keypairResidents, packetResidents,
      identityView, Unique, Absent, ResidentUnique]
  refine ⟨hr, ⟨hr.1.peer, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Bounded, Peers.snapshot, deviceDropped]
  · intro stamp released
    rcases ho.peer stamp released with old | ⟨i, live⟩
    · exact hi.peer.pastBounded stamp old
    · exact hi.peer.bounded i stamp live
  · simp [deviceDropped]
  · simp [Bounded, keyStore, keypairResidents, deviceDropped]
  · intro stamp released
    rcases ho.key stamp released with old | ⟨i, live⟩
    · exact hi.keyPast stamp old
    · exact hi.keyBounded i stamp live
  · simp [deviceDropped]
  · simp [deviceDropped]
  · simp [deviceDropped]
  · intro stamp released
    rcases ho.packet stamp released with old | ⟨i, live⟩
    · exact hi.packetPastEpoch stamp old
    · obtain ⟨d,n,hd,rfl,_⟩ := packet_resident_store live
      exact hi.epochBounded d hd
  · simp [deviceDropped]

theorem dropDevicePrefix_allocation :
    PrefixPreserves AllocationInv LifetimeEvent.Safe dropDevicePrefix := by
  intro w h hi
  exact ⟨deviceRetirementEvents w, rfl, hi.dropDevice.safe, hi.dropDevice⟩

end Leanux.Proofs.WG.Lifetimes
