import Leanux.Proofs.WG.Lifetimes.AllocationReleaseFrames

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Lifting the existing release observers. Their exact event equations supply
release origins; no observer control flow is copied or replaced here. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem ReleaseOrigin.append (ho : ReleaseOrigin [] events w) : ReleaseOrigin h (h ++ events) w := by
  constructor
  all_goals intro stamp hs
  all_goals rw [List.filterMap_append, AccessEvent.released_append] at hs
  all_goals rcases hs with old | new
  all_goals try exact Or.inl old
  · right; simpa [AccessEvent.Released] using ho.peer stamp new
  · right; simpa [AccessEvent.Released] using ho.key stamp new
  · right; simpa [AccessEvent.Released] using ho.packet stamp new

theorem ReleaseOrigin.refl (h : List LifetimeEvent) (w : World) : ReleaseOrigin h h w :=
  ⟨fun _ hi => Or.inl hi, fun _ hi => Or.inl hi, fun _ hi => Or.inl hi⟩

theorem peerPut_origin (id : Option PeerId) (w : World) (h : List LifetimeEvent) :
    ReleaseOrigin h (runPrefix (peerPutMixed id) w h).2 w := by
  rw [peerPutMixed_run]
  apply ReleaseOrigin.append
  constructor
  · intro stamp hs
    have hp : AccessEvent.Released (Peers.peerPutEvents id w) stamp := by
      simpa [filterMap_encoded LifetimeEvent.peer LifetimeEvent.peer? (fun _ => rfl)] using hs
    obtain ⟨i, p, _, live, _, rfl⟩ := Peers.peerPutEvents_release id w stamp hp
    right; exact ⟨i, by change (w.k.wg.bind (fun d => d.peers[i]?)).map (·.internalId) = _; rw [live]; rfl⟩
  · simp [ReleasedFrom, filterMap_disjoint LifetimeEvent.peer LifetimeEvent.keypair? (fun _ => rfl), AccessEvent.Released]
  · simp [ReleasedFrom, filterMap_disjoint LifetimeEvent.peer LifetimeEvent.packet? (fun _ => rfl), AccessEvent.Released]

theorem peerGet_origin (id : PeerId) (w : World) (h : List LifetimeEvent) :
    ReleaseOrigin h (runPrefix (peerGetMixed id) w h).2 w := by
  have hr := focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer?
    (peerGetLocal id) w h _ _ (peerGetLocal_run id w _)
  change ReleaseOrigin h (runPrefix (focusPrefix _ _ _) w h).2 w
  rw [hr]
  apply ReleaseOrigin.append
  have noRelease : ∀ stamp, ¬ AccessEvent.Released (peerGetEvents id w) stamp := by
    intro stamp
    unfold peerGetEvents
    split
    · simp [AccessEvent.Released]
    · split <;> simp [AccessEvent.Released]
  constructor
  · intro stamp hs
    exact False.elim (noRelease stamp (by
      simpa [filterMap_encoded LifetimeEvent.peer LifetimeEvent.peer? (fun _ => rfl)] using hs))
  · simp [ReleasedFrom, filterMap_disjoint LifetimeEvent.peer LifetimeEvent.keypair? (fun _ => rfl), AccessEvent.Released]
  · simp [ReleasedFrom, filterMap_disjoint LifetimeEvent.peer LifetimeEvent.packet? (fun _ => rfl), AccessEvent.Released]

theorem keypairPut_origin (kp : Option KeypairId) (now : Bool) (w : World) (h : List LifetimeEvent) :
    ReleaseOrigin h (runPrefix (keypairPutPrefix kp now) w h).2 w := by
  rw [keypairPutPrefix_run]
  apply ReleaseOrigin.append
  unfold keypairPutEvents
  cases hx : kp.bind (fun i => (w.k.wg.bind fun d => d.keypairs[i]?).map (fun k => (i, k))) with
  | none => exact ReleaseOrigin.refl [] w
  | some pair =>
    rcases pair with ⟨i, k⟩
    have live : keypairResidents w i = some k.internalId := by
      cases kp with
      | none => simp at hx
      | some j =>
        cases hk : w.k.wg.bind (fun d => d.keypairs[j]?) with
        | none => simp only [Option.bind_some, hk, Option.map_none] at hx; cases hx
        | some old =>
          simp only [Option.bind_some, hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
          rcases hx with ⟨rfl, rfl⟩
          change (w.k.wg.bind (fun d => d.keypairs[j]?)).map (·.internalId) = _
          rw [hk]; rfl
    simp only
    split
    all_goals constructor
    all_goals simp [ReleasedFrom, List.filterMap_cons, List.filterMap_nil,
      LifetimeEvent.peer?, LifetimeEvent.keypair?, LifetimeEvent.packet?, AccessEvent.Released]
    exact ⟨i, live⟩

theorem peerGetMixed_allocation (id : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (peerGetMixed id) :=
  allocation_retained (releaseAmbient.peerGet id) (peerGetMixed_erases id)
    (fun w _ v hr => peerGet_retention id w v hr) (peerGet_origin id)

theorem peerPutMixed_allocation (id : Option PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (peerPutMixed id) :=
  allocation_retained (releaseAmbient.peerPut id) (peerPutMixed_erases id)
    (fun w _ v hr => peerPut_retention id w v hr) (peerPut_origin id)

theorem keypairPutPrefix_allocation (kp : Option KeypairId) (now : Bool) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (keypairPutPrefix kp now) :=
  allocation_retained (keypairPutPrefix_preserves kp now) (keypairPutPrefix_erases kp now)
    (fun w _ v hr => keypairPut_retention kp now w v hr) (keypairPut_origin kp now)

theorem erasePacket_retention (slot : Packets.Slot) (w : World) :
    AllocationRetention w (Packets.update w (erasePacketDevice slot)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases slot <;> simp [allocationMetadata, deviceAllocationMetadata, Packets.update,
      erasePacketDevice, Option.map_map, Function.comp_def]
    all_goals rfl
  · have he : Peers.snapshot (Packets.update w (erasePacketDevice slot)) = Peers.snapshot w := by
      cases slot <;> simp [Peers.snapshot, Packets.update, erasePacketDevice, Option.bind_map, Function.comp_def]
    rw [he]; exact Retained.refl _
  · intro i stamp hi
    cases slot <;> simpa [keypairResidents, Packets.update, erasePacketDevice,
      Option.bind_map, Function.comp_def] using hi
  · intro i stamp hi
    cases hd : w.k.wg with
    | none => simp [packetResidents, Packets.update, hd] at hi
    | some d =>
      cases slot <;> cases i <;>
        simp only [packetResidents, Packets.update, hd, Option.map_some, Option.bind_some,
          erasePacketDevice, Std.TreeMap.getElem?_erase, Std.LawfulEqOrd.compare_eq_iff_eq] at hi ⊢
      all_goals first | exact hi | (split at hi <;> simp_all)

theorem freeTxSkb_retention (id : SkbId) (w v : World)
    (hr : (freeTxSkb id).run w = .ok (x, v)) : AllocationRetention w v := by
  cases x
  cases hd : w.k.wg with
  | none => simp [freeTxSkb, getTxSkb, getDev, getK, hd, invariant] at hr
  | some d =>
    cases hp : d.txSkbs[id]? with
    | none => simp [freeTxSkb, getTxSkb, getDev, getK, hd, hp, invariant] at hr
    | some p =>
      rw [Packets.freeTxSkb_run w d id p hd hp] at hr
      cases hr; exact erasePacket_retention (.inl id) w

theorem freeRxSkb_retention (id : SkbId) (w v : World)
    (hr : (freeRxSkb id).run w = .ok (x, v)) : AllocationRetention w v := by
  cases x
  cases hd : w.k.wg with
  | none => simp [freeRxSkb, getRxSkb, getDev, getK, hd, invariant] at hr
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none => simp [freeRxSkb, getRxSkb, getDev, getK, hd, hp, invariant] at hr
    | some p =>
      rw [Packets.freeRxSkb_run w d id p hd hp] at hr
      cases hr; exact erasePacket_retention (.inr id) w

theorem freeTxSkb_origin (id : SkbId) (w : World) (h : List LifetimeEvent) :
    ReleaseOrigin h (runPrefix (freeTxSkbPrefix id) w h).2 w := by
  rw [freeTxSkbPrefix_run]
  cases hg : (getTxSkb id).run w with
  | error e => exact ReleaseOrigin.refl h w
  | ok out =>
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getTxSkb_current id w out.2 out.1 hg
    apply ReleaseOrigin.append
    constructor
    all_goals simp [ReleasedFrom, List.filterMap_cons, List.filterMap_nil,
      LifetimeEvent.peer?, LifetimeEvent.keypair?, LifetimeEvent.packet?, AccessEvent.Released]
    exact ⟨.inl id, by simp [packetResidents, packetStamp, hd, hp]⟩

theorem freeRxSkb_origin (id : SkbId) (w : World) (h : List LifetimeEvent) :
    ReleaseOrigin h (runPrefix (freeRxSkbPrefix id) w h).2 w := by
  rw [freeRxSkbPrefix_run]
  cases hg : (getRxSkb id).run w with
  | error e => exact ReleaseOrigin.refl h w
  | ok out =>
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getRxSkb_current id w out.2 out.1 hg
    apply ReleaseOrigin.append
    constructor
    all_goals simp [ReleasedFrom, List.filterMap_cons, List.filterMap_nil,
      LifetimeEvent.peer?, LifetimeEvent.keypair?, LifetimeEvent.packet?, AccessEvent.Released]
    exact ⟨.inr id, by simp [packetResidents, packetStamp, hd, hp]⟩

theorem freeTxSkbPrefix_allocation (id : SkbId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (freeTxSkbPrefix id) :=
  allocation_retained (freeTxSkbPrefix_preserves id) (freeTxSkbPrefix_erases id)
    (fun w _ v hr => freeTxSkb_retention id w v hr) (freeTxSkb_origin id)

theorem freeRxSkbPrefix_allocation (id : SkbId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (freeRxSkbPrefix id) :=
  allocation_retained (freeRxSkbPrefix_preserves id) (freeRxSkbPrefix_erases id)
    (fun w _ v hr => freeRxSkb_retention id w v hr) (freeRxSkb_origin id)

end Leanux.Proofs.WG.Lifetimes
