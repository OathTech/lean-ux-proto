import Leanux.Proofs.WG.Origins.CurrentIdentity
import Leanux.Proofs.WG.Origins.RetainingConfiguration

/-! Creation retains the current identity of old receiving-key owners when
those words lie below the entry peer frontier. The fresh slot may overwrite an
arbitrary resident at the frontier; no claim about that resident is needed. -/
namespace Leanux.Proofs.WG.CurrentIdentity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes

private def BelowCells (before after : ConfiguredIdentity.State) : Prop :=
  ∀ (pid : PeerId) (cell : ConfiguredIdentity.Cell), pid < before.frontier →
    after.peers pid = some cell → ∃ old, before.peers pid = some old ∧
      (cell.stamp, cell.static) = (old.stamp, old.static)

private theorem belowCells_refl (s : ConfiguredIdentity.State) : BelowCells s s :=
  fun _ cell _ hp => ⟨cell, hp, rfl⟩

private theorem belowCells_allocate (s : ConfiguredIdentity.State) (key : Key) (stamp : Nat) :
    BelowCells s (s.allocate key stamp) := by
  intro pid cell bound hp
  have ne : s.frontier ≠ pid := Ne.symm (Nat.ne_of_lt bound)
  exact ⟨cell, by simpa [ConfiguredIdentity.State.allocate, ne] using hp, rfl⟩

private theorem belowCells_setWord {before after : ConfiguredIdentity.State}
    (h : BelowCells before after) (pid : PeerId) (word : Option PeerId) :
    BelowCells before (after.setWord pid word) := by
  intro q cell bound hp
  by_cases eq : pid = q
  · subst q
    have mapped : (after.peers pid).map (fun p => {p with word}) = some cell := by
      simpa [ConfiguredIdentity.State.setWord] using hp
    obtain ⟨old, ho, rfl⟩ := Option.map_eq_some_iff.mp mapped
    obtain ⟨original, stored, same⟩ := h pid old bound ho
    exact ⟨original, stored, same⟩
  · exact h q cell bound (by simpa [ConfiguredIdentity.State.setWord, eq] using hp)

/-- Every normal result, including allocation refusal, retains complete old
peer identities below the entry frontier. Initializer writes are included. -/
theorem peerCreate_below (key : Key) (psk : Option Key) (w v : WGWorld)
    (ambient ambient' : Ambient) (result : Except Int PeerId) (before after : Device)
    (hw : w.dev = some before) (hv : v.dev = some after)
    (hr : ((peerCreate key psk).run w).run ambient = .ok ((result, v), ambient')) :
    BelowRetained before after := by
  let start := ConfiguredIdentity.state before
  let P := fun u : WGWorld => ConfiguredIdentity.view u = some start
  let Q := fun u : WGWorld => ∃ s, ConfiguredIdentity.view u = some s ∧ BelowCells start s
  have getter : Hoare getDev P (fun d u => P u ∧ ConfiguredIdentity.state d = start) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u a d out b hu hrun
    cases hd : u.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hrun
      cases hrun
    | some saved =>
      simp [getDev, hd] at hrun
      rcases hrun with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨hu, Option.some.inj (by simpa [P, ConfiguredIdentity.view, hd] using hu)⟩
  have ambient_rule {α : Type} (a : AmbientM α) (R : WGWorld → Prop) :
      Preserves R (StateT.lift a) := hoare_liftAmbient a R
  have failure (d : Device) : Hoare (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId))
      (fun u => P u ∧ ConfiguredIdentity.state d = start) (fun _ => Q) := by
    apply hoare_consequence (hoare_pure (Except.error (-ENOMEM) : Except Int PeerId) _)
    · intro _ h; exact h
    · intro _ u h
      exact ⟨start, h.2.1, belowCells_refl _⟩
  have init (pid : PeerId) : Preserves Q (handshakeInit pid psk) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u a x out b hi hrun
    cases x
    obtain ⟨s, hs, hb⟩ := hi
    have effect := ConfiguredIdentity.handshakeInit_effect pid psk u out a b hrun
    rw [hs, Option.map_some] at effect
    exact ⟨s.setWord pid (some pid), effect, belowCells_setWord hb _ _⟩
  have publish (pid : PeerId) : Preserves Q (ConfiguredIdentity.publishRow pid key) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u a x out b hi hrun
    cases x
    obtain ⟨s, hs, hb⟩ := hi
    have effect := ConfiguredIdentity.publishRow_effect pid key u out a b hrun
    rw [hs, Option.map_some] at effect
    exact ⟨s.insertRow key pid, effect, hb⟩
  have proof : Hoare (peerCreate key psk) P (fun _ => Q) := by
    rw [← Peers.peerCreateFactored_eq]
    unfold Peers.peerCreateFactored
    apply hoare_bind _ _ getter
    intro d
    apply hoare_bind _ _ (ambient_rule (AmbientM.branchCmp .peerCreateMaxPeers
      (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE)
      (fun u => P u ∧ ConfiguredIdentity.state d = start))
    intro maxPeers
    cases maxPeers with
    | true => exact failure d
    | false =>
      apply hoare_bind _ _ (ambient_rule (AmbientM.hiddenAlloc .kmemCacheZallocPeer)
        (fun u => P u ∧ ConfiguredIdentity.state d = start))
      intro allocated
      apply hoare_bind _ _ (ambient_rule (AmbientM.branch .peerCreateNoMem !allocated)
        (fun u => P u ∧ ConfiguredIdentity.state d = start))
      intro noMem
      cases noMem with
      | true => exact failure d
      | false =>
        apply hoare_bind _ _ (ambient_rule (AmbientM.branch .peerCreateDstCacheFail false)
          (fun u => P u ∧ ConfiguredIdentity.state d = start))
        intro cacheFailed
        cases cacheFailed with
        | true => exact failure d
        | false =>
          have core : Hoare (Peers.peerCreateCore d.nextPeer key)
              (fun u => P u ∧ ConfiguredIdentity.state d = start) (fun _ => Q) := by
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro u a x out b hi hrun
            rw [Peers.peerCreateCore_run] at hrun
            cases hrun
            obtain ⟨dev, hdev, hs⟩ := Option.map_eq_some_iff.mp hi.1
            have next : d.nextPeer = dev.nextPeer :=
              congrArg ConfiguredIdentity.State.frontier (hi.2.trans hs.symm)
            rw [next]
            refine ⟨(ConfiguredIdentity.state dev).allocate key (u.peerCounter + 1),
              ConfiguredIdentity.core_state u dev key hdev, ?_⟩
            rw [← hs]
            exact belowCells_allocate _ _ _
          apply hoare_bind _ _ core
          intro _
          apply hoare_bind _ _ ((ConfiguredIdentity.cacheReset d.nextPeer).wp
            (fun view => ∃ s, view = some s ∧ BelowCells start s))
          intro _
          apply preserves_bind (init d.nextPeer)
          intro _
          apply preserves_bind ((ConfiguredIdentity.resetHandshake d.nextPeer).wp
            (fun view => ∃ s, view = some s ∧ BelowCells start s))
          intro _
          apply preserves_bind (publish d.nextPeer)
          intro _
          exact preserves_pure _
  obtain ⟨s, hs, hb⟩ := (hoare_iff_run_ambient _ _ _).mp proof w ambient result v ambient'
    (by simp [P, start, ConfiguredIdentity.view, hw]) hr
  have eq : s = ConfiguredIdentity.state after :=
    Option.some.inj (hs.symm.trans (by simp [ConfiguredIdentity.view, hv]))
  subst s
  intro pid peer bound resident
  obtain ⟨oldCell, stored, same⟩ := hb pid (ConfiguredIdentity.cell peer) bound
    (by simp [ConfiguredIdentity.state, resident])
  have mapped : (before.peers[pid]?).map ConfiguredIdentity.cell = some oldCell := stored
  obtain ⟨old, oldResident, cellEq⟩ := Option.map_eq_some_iff.mp mapped
  subst oldCell
  exact ⟨old, oldResident, same⟩

/-- The only owner bound used by creation transport. Invalid receiving keys
need no bound because they impose no current-support obligation. -/
def ReceivingOwnersBelow (w : WGWorld) : Prop :=
  ∀ d, w.dev = some d → ∀ (slot : KeypairId) (key : Keypair),
    d.keypairs[slot]? = some key → key.receiving.isValid = true →
    ∀ pid, key.peer = some pid → pid < d.nextPeer

theorem receivingOwnersBelow_of_affiliation (hi : Affiliation.Inv w) : ReceivingOwnersBelow w := by
  intro d hd slot key hk _ pid word
  have inv := hi (Affiliation.state d) (by simp [Affiliation.view, hd])
  exact inv.words slot key.internalId pid
    (by simp [Affiliation.state, Affiliation.keyCell, hk, word])

theorem peerCreate_retains (key : Key) (psk : Option Key) (w v : WGWorld)
    (ambient ambient' : Ambient) (result : Except Int PeerId) (bounded : ReceivingOwnersBelow w)
    (hr : ((peerCreate key psk).run w).run ambient = .ok ((result, v), ambient')) : Retains w v := by
  have material : Origins.view v = Origins.view w :=
    (ProjectedAction.iff_run_ambient _ _ _).mp (Origins.Retaining.peerCreate_material key psk)
      w ambient result v ambient' hr
  intro after ha slot current hc valid
  have oldView : Origins.view w = some (after.ifindex, fun id => after.keypairs[id]?) :=
    material.symm.trans (by simp [Origins.view, ha])
  obtain ⟨before, hw, fields⟩ := Option.map_eq_some_iff.mp oldView
  have epoch := congrArg Prod.fst fields
  have keys := congrFun (congrArg Prod.snd fields) slot
  have oldKey : before.keypairs[slot]? = some current := keys.trans hc
  refine ⟨before, current, hw, epoch, oldKey, valid, Origins.KeyLe.refl _, ?_⟩
  intro pid peer word resident
  exact peerCreate_below key psk w v ambient ambient' result before after hw ha hr
    pid peer (bounded before hw slot current oldKey valid pid word) resident

theorem peerCreate_retains_of_affiliation (key : Key) (psk : Option Key) (w v : WGWorld)
    (ambient ambient' : Ambient) (result : Except Int PeerId) (hi : Affiliation.Inv w)
    (hr : ((peerCreate key psk).run w).run ambient = .ok ((result, v), ambient')) : Retains w v :=
  peerCreate_retains key psk w v ambient ambient' result (receivingOwnersBelow_of_affiliation hi) hr

theorem peerCreate_current (key : Key) (psk : Option Key) (history : List SessionOrigin.Receipt) :
    Hoare (peerCreate key psk) (fun w => Inv history w ∧ ReceivingOwnersBelow w)
      (fun _ w => Inv history w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  exact hi.1.retain (peerCreate_retains key psk w v ambient ambient' result hi.2 hr)

end Leanux.Proofs.WG.CurrentIdentity
