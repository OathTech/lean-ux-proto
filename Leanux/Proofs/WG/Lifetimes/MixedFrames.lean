import Leanux.Proofs.WG.Lifetimes.MixedAccess

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Cross-family frames for focused peer observers. Local event safety does
not on its own transport the other stores; their original-call frame is an
explicit additional premise. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def otherResidents (w : WGWorld) := (keypairResidents w, packetResidents w)

theorem peerFocus_preserves {S α : Type} (project : S → WGWorld)
    {g : PrefixT Peers.PeerEvent S α} {a : StateT S (Except Stop) α}
    (hg : PrefixPreserves (fun h w => Peers.AccessInv h (project w)) AccessEvent.Safe g)
    (he : ErasesPrefix g a) (ha : SameView (otherResidents ∘ project) a) :
    PrefixPreserves (fun h w => MixedInv h (project w)) LifetimeEvent.Safe (peerFocus g) := by
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
      have hx := (ProjectedAction.iff_run _ _ _).mp ha w out.1 out.2 ((he w _).symm.trans ho)
      have keyeq := congrArg Prod.fst hx
      have packeq := congrArg Prod.snd hx
      change keypairResidents (project out.2) = keypairResidents (project w) at keyeq
      change packetResidents (project out.2) = packetResidents (project w) at packeq
      constructor
      · simpa only [hp, hsuf, ho] using hout
      · simpa only [hk, keyeq] using hi.keypair
      · simpa only [ht, packeq] using hi.packet

theorem peerStateFocus_preserves {g : WGPrefix Peers.PeerEvent α} {a : WG.M α}
    (hg : StatePrefixPreserves (fun h w _ => Peers.AccessInv h w) AccessEvent.Safe g)
    (he : ErasesStatePrefix g a) (ha : SameView otherResidents a) :
    StatePrefixPreserves (fun h w _ => MixedInv h w) LifetimeEvent.Safe (peerStateFocus g) := by
  intro w ambient h hi
  obtain ⟨suffix, hsuf, hsafe, hout⟩ := hg w ambient (h.filterMap LifetimeEvent.peer?) hi.peer
  have hr : runPrefix (g w) ambient (h.filterMap LifetimeEvent.peer?) =
      ((runPrefix (g w) ambient (h.filterMap LifetimeEvent.peer?)).1,
        h.filterMap LifetimeEvent.peer? ++ suffix) := Prod.ext rfl hsuf
  unfold peerStateFocus
  dsimp only [focusStatePrefix, StateT.run] at *
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
  · cases ho : (runPrefix (g w) ambient (h.filterMap LifetimeEvent.peer?)).1 with
    | error e => trivial
    | ok out =>
      have hx := (ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient out.1.1 out.1.2 out.2 ((he w ambient _).symm.trans ho)
      have keyeq := congrArg Prod.fst hx
      have packeq := congrArg Prod.snd hx
      change keypairResidents out.1.2 = keypairResidents w at keyeq
      change packetResidents out.1.2 = packetResidents w at packeq
      constructor
      · simpa only [hp, hsuf, ho] using hout
      · simpa only [hk, keyeq] using hi.keypair
      · simpa only [ht, packeq] using hi.packet

theorem peerPut_otherResidents (id : Option PeerId) : SameView otherResidents (peerPut id) := by
  apply SameView.of_wp
  intro s
  have index_spec (a : IndexM Unit) :
      Hoare (MonadLift.monadLift a : WG.M Unit)
        (fun w => otherResidents w = s) (fun _ w => otherResidents w = s) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    have same : otherResidents {w with dev := some {d with indexTable := table}} =
        otherResidents w := by
      unfold otherResidents keypairResidents packetResidents
      simp only [hd, Option.bind_some]
    exact same.trans hi
  unfold Hoare at index_spec
  mvcgen [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
    refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    index_spec, retirePeerUnits, modifyAmbient, invariant, unsupported,
    AmbientM.invariant, AmbientM.unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold otherResidents at *
  all_goals unfold keypairResidents packetResidents at *
  all_goals simp_all [Option.bind_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all [Option.bind_map, Function.comp_def]

theorem peerPutMixed_preserves (id : Option PeerId) :
    StatePrefixPreserves (fun h w _ => MixedInv h w) LifetimeEvent.Safe (peerPutMixed id) :=
  peerStateFocus_preserves (Peers.peerPutPrefix_preserves id) (Peers.peerPutPrefix_erases id)
    (peerPut_otherResidents id)

theorem setRxSkb_identity (id : SkbId) (f : RxPacket → RxPacket) :
    SameView identityView (setRxSkb id f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  cases hd : w.dev with
  | none => simp [setRxSkb, liftSkb_run, hd] at hr
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none =>
      simp [setRxSkb, liftSkb_run, SkbStore.setRx, SkbStore.getRx,
        hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      rw [Packets.setRxSkb_run w ambient d id p f hd hp] at hr
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
  intro w ambient h hi
  change ∃ suffix, _ ∧ _ ∧ _
  rw [show runPrefix ((setRxSkbPrefix id f).run w) ambient h =
    runStatePrefix (setRxSkbPrefix id f) w ambient h from rfl, setRxSkbPrefix_run]
  cases hr : ((getRxSkb id).run w).run ambient with
  | error _ => exact ⟨[], by simp, hi.1.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, d, hd, hp⟩ := Packets.getRxSkb_current id w v p ambient ambient' hr
    have live : packetResidents v (.inr id) = some (packetStamp v id) := by
      simp [packetResidents, packetStamp, hd, hp]
    have hn := (hi.1.packetRead live).packetWrite live
    have hs : ((setRxSkb id f).run v).run ambient' =
        .ok (((), Packets.update v fun d =>
          {d with rxSkbs := d.rxSkbs.insert id (f p)}), ambient') :=
      Packets.setRxSkb_run v ambient' d id p f hd hp
    rw [hs]
    have he := (ProjectedAction.iff_run_ambient _ _ _).mp
      (setRxSkb_identity id f) v ambient' () _ ambient' hs
    refine ⟨[.packet (.read (.inr id) (packetStamp v id)),
      .packet (.write (.inr id) (packetStamp v id))], rfl, ?_, ?_, he ▸ hi.2⟩
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn.safe
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn.congr he

end Leanux.Proofs.WG.Lifetimes
