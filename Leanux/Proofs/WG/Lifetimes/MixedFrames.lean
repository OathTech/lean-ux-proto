import Leanux.Proofs.WG.Lifetimes.MixedAccess

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Cross-family frames for focused peer observers. Local event safety does
not on its own transport the other stores; their original-call frame is an
explicit additional premise. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def otherResidents (w : World) := (keypairResidents w, packetResidents w)

theorem peerFocus_preserves (hg : PrefixPreserves Peers.AccessInv AccessEvent.Safe g)
    (he : ErasesPrefix g a) (ha : SameView otherResidents a) :
    PrefixPreserves MixedInv LifetimeEvent.Safe (peerFocus g) := by
  intro w h hi
  obtain ⟨suffix, hsuf, hsafe, hout⟩ := hg w (h.filterMap LifetimeEvent.peer?) hi.peer
  have hr : runPrefix g w (h.filterMap LifetimeEvent.peer?) =
      ((runPrefix g w (h.filterMap LifetimeEvent.peer?)).1,
        h.filterMap LifetimeEvent.peer? ++ suffix) := Prod.ext rfl hsuf
  unfold peerFocus
  rw [focusPrefix_suffix _ _ _ _ _ _ _ hr]
  have hp : (h ++ suffix.map LifetimeEvent.peer).filterMap LifetimeEvent.peer? =
      h.filterMap LifetimeEvent.peer? ++ suffix := by
    rw [List.filterMap_append, filterMap_encoded LifetimeEvent.peer LifetimeEvent.peer? (fun _ => rfl)]
  have hk : (h ++ suffix.map LifetimeEvent.peer).filterMap LifetimeEvent.keypair? =
      h.filterMap LifetimeEvent.keypair? := by
    rw [List.filterMap_append, filterMap_disjoint _ _ (fun _ => rfl), List.append_nil]
  have ht : (h ++ suffix.map LifetimeEvent.peer).filterMap LifetimeEvent.packet? =
      h.filterMap LifetimeEvent.packet? := by
    rw [List.filterMap_append, filterMap_disjoint _ _ (fun _ => rfl), List.append_nil]
  refine ⟨suffix.map LifetimeEvent.peer, rfl, ?_, ?_⟩
  · exact ⟨by simpa only [hp, hsuf] using hsafe, hk ▸ hi.keypair.1, ht ▸ hi.packet.1⟩
  · cases ho : (runPrefix g w (h.filterMap LifetimeEvent.peer?)).1 with
    | error e => trivial
    | ok out =>
      have hx := ha w out.1 out.2 ((he w _).symm.trans ho)
      have keyeq := congrArg Prod.fst hx
      have packeq := congrArg Prod.snd hx
      change keypairResidents out.2 = keypairResidents w at keyeq
      change packetResidents out.2 = packetResidents w at packeq
      constructor
      · simpa only [hp, hsuf, ho] using hout
      · simpa only [hk, keyeq] using hi.keypair
      · simpa only [ht, packeq] using hi.packet

theorem peerPut_otherResidents (id : Option PeerId) : SameView otherResidents (peerPut id) := by
  apply SameView.of_wp
  intro s
  simp only [peerPut, indexRemove_eq, indexUnhash]
  mvcgen [peerPut, requireNotPending, getPeer, getDev, getK, setPeer,
    modifyDev, modifyK, refcountDecAndTest, branch, branchCmp,
    indexRemove, retirePeerUnits, invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold otherResidents at *
  all_goals unfold keypairResidents packetResidents at *
  all_goals simp_all
  all_goals subst_vars
  all_goals simp_all

theorem peerPutMixed_preserves (id : Option PeerId) :
    PrefixPreserves MixedInv LifetimeEvent.Safe (peerPutMixed id) :=
  peerFocus_preserves (Peers.peerPutPrefix_preserves id) (Peers.peerPutPrefix_erases id)
    (peerPut_otherResidents id)

theorem setRxSkb_identity (id : SkbId) (f : RxPacket → RxPacket) :
    SameView identityView (setRxSkb id f) := by
  intro w x v hr
  cases x
  cases hd : w.k.wg with
  | none => simp [setRxSkb, getRxSkb, getDev, getK, hd, invariant] at hr
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none => simp [setRxSkb, getRxSkb, getDev, getK, hd, hp, invariant] at hr
    | some p =>
      rw [Packets.setRxSkb_run w d id p f hd hp] at hr
      cases hr
      apply Prod.ext
      · simp [identityView, Peers.snapshot, Packets.update, hd]
      · apply Prod.ext
        · unfold identityView keypairResidents
          simp [Packets.update, hd]
        · funext slot
          cases slot with
          | inl j => simp [identityView, packetResidents, Packets.update, hd]
          | inr j =>
            by_cases hj : id = j
            · subst j
              simp [identityView, packetResidents, Packets.update, hd, hp]
            · simp [identityView, packetResidents, Packets.update, hd,
                Std.TreeMap.getElem?_insert, hj]

theorem mixed_setRxSkb (P : IdentityView → Prop) (id : SkbId) (f : RxPacket → RxPacket) :
    MixedSpec P (setRxSkbPrefix id f) (fun _ => P) := by
  intro w h hi
  rw [setRxSkbPrefix_run]
  cases hr : (getRxSkb id).run w with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨p, v⟩
    obtain ⟨rfl, d, hd, hp⟩ := Packets.getRxSkb_current id w v p hr
    have live : packetResidents v (.inr id) = some (packetStamp v id) := by
      simp [packetResidents, packetStamp, hd, hp]
    have hn := (hi.1.packetRead live).packetWrite live
    have hs : (setRxSkb id f).run v = .ok ((), Packets.update v fun d =>
        {d with rxSkbs := d.rxSkbs.insert id (f p)}) := Packets.setRxSkb_run v d id p f hd hp
    rw [hs]
    have he := setRxSkb_identity id f v () _ hs
    refine ⟨[.packet (.read (.inr id) (packetStamp v id)),
      .packet (.write (.inr id) (packetStamp v id))], rfl, ?_, ?_, he ▸ hi.2⟩
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn.safe
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn.congr he

end Leanux.Proofs.WG.Lifetimes
