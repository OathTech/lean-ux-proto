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
  intro initial
  let P := fun w : WGWorld => otherResidents w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have index (a : IndexM Unit) : Preserves P (monadLift a : WG.M Unit) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    change otherResidents _ = initial
    change otherResidents w = initial at hi
    rw [← hi]
    clear hi
    unfold otherResidents
    apply Prod.ext
    · funext j; simp [keypairResidents, hd]
    · funext j; cases j <;> simp [packetResidents, hd]
  have read (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' hi hr
    have h := (Peers.getPeer_current pid w v p ambient ambient' hr).1
    simpa only [h] using hi
  have write (f : Device → Device)
      (he : ∀ d, (f d).ifindex = d.ifindex)
      (hk : ∀ d, (f d).keypairs = d.keypairs)
      (ht : ∀ d, (f d).txSkbs = d.txSkbs)
      (hr : ∀ d, (f d).rxSkbs = d.rxSkbs) : Preserves P (modifyDev f) := by
    unfold modifyDev
    apply hoare_modify
    intro w hi
    change otherResidents _ = initial
    change otherResidents w = initial at hi
    rw [← hi]
    clear hi
    unfold otherResidents
    apply Prod.ext
    · funext j
      simp [keypairResidents, Option.bind_map, Function.comp_def, hk]
    · funext j
      cases j <;> simp [packetResidents, Option.bind_map, Function.comp_def, he, ht, hr]
  have release (count : Nat) : Preserves P (refcountDecAndTest count : WG.M Bool) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' hi hr
    by_cases pos : 0 < count <;> by_cases one : count = 1 <;>
      by_cases zero : count = 0 <;> by_cases under : count < 1 <;>
      simp [refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        unsupported, AmbientM.unsupported, pos, one, zero, under] at hr
    all_goals try (change Except.error _ = Except.ok _ at hr; cases hr)
    all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact hi
  have branchRule {α : Type} (decision : Decision) (value : Bool)
      (f : Bool → WG.M α) (hf : Preserves P (f value)) :
      Preserves P ((branch decision value : WG.M Bool) >>= f) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hi hr
    change ((f value).run w).run _ = .ok ((x, v), ambient') at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hi hr
  change Preserves P (peerPut id)
  cases id with
  | none =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hi hr
    simp [peerPut, branch, AmbientM.branch] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact hi
  | some pid =>
    unfold peerPut
    apply branchRule .peerPutNull false
    simp only [Bool.false_eq_true, ↓reduceIte, requireNotPending, pure_bind]
    apply preserves_bind (read pid)
    intro p
    apply preserves_bind (write (fun d => {d with peers := d.peers.insert pid {p with refcount := p.refcount - 1}})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    intro _
    apply preserves_bind (release p.refcount)
    intro released
    apply branchRule .peerKrefPutReleased released
    cases released <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact preserves_pure ()
    · apply preserves_bind (index (indexRemove (.handshake pid)))
      intro _
      split
      · apply (hoare_iff_run_ambient _ _ _).mpr
        intro w ambient x v ambient' _ hr
        cases hr
      · apply preserves_bind (write
          (fun d => {d with txDropped := d.txDropped + p.staged.length, peers := d.peers.erase pid})
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
        intro _
        split
        · apply (hoare_iff_run_ambient _ _ _).mpr
          intro w ambient x v ambient' _ hr
          cases hr
        · unfold retirePeerUnits modifyAmbient
          apply preserves_bind (ambient (modify _ : AmbientM Unit))
          intro _
          apply hoare_modify
          intro w hi
          exact hi

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
