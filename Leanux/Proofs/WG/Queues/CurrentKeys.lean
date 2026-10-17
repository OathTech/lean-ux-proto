import Leanux.Proofs.WG.Origins.OwnerCreation
import Leanux.Proofs.WG.Origins.OwnerCompletion

/-! Current-slot compatibility needs a reference frontier as well as nullable
ownership. These are supplied-state normal-endpoint contracts; no stopped
execution is assigned a WGWorld and no initialized whole-run closure is claimed. -/
namespace Leanux.Proofs.WG.CurrentKeys
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues.RxCredits

def Below (w : WGWorld) : Prop :=
  ∀ (d : Device) (pid : PeerId) (p : Peer) (kid : KeypairId),
    w.dev = some d → d.peers[pid]? = some p →
    p.keypairCurrent = some kid → kid < d.nextKeypairId

structure Inv (w : WGWorld) : Prop where
  compatible : CurrentsCompatible w
  below : Below w

theorem of_affiliation (hi : Affiliation.Inv w) : Inv w := by
  refine ⟨currentsCompatible_of_affiliation hi, ?_⟩
  intro d pid p kid hd hp hk
  have h := hi (Affiliation.state d) (by simp [Affiliation.view, hd])
  exact (h.slots pid (Affiliation.peerCell p) kid
    (by simp [Affiliation.state, hp]) (Or.inl hk)).1

theorem initial (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) : Inv w :=
  of_affiliation (Affiliation.initial net bare w hw)

theorem owner_keys (owner : OwnerBounds.Carrier w) (current : Inv w) :
    KeysCompatible w := ⟨owner.compatible, current.compatible⟩

theorem allocate (hi : Inv w) (hd : w.dev = some d) (word : Option PeerId) :
    Inv (keyAllocationWorld w d word) := by
  constructor
  · intro pid after p kid ha hp hc other key hb hk
    have ea : after = keyAllocationDevice d (w.keypairCounter + 1) word :=
      Option.some.inj ha.symm
    have eb : other = after := Option.some.inj (hb.symm.trans ha)
    subst other
    subst after
    have oldPeer : d.peers[pid]? = some p := hp
    have below := hi.below d pid p kid hd oldPeer hc
    have oldKey : d.keypairs[kid]? = some key := by
      simpa [keyAllocationDevice, Std.TreeMap.getElem?_insert,
        Ne.symm (Nat.ne_of_lt below)] using hk
    exact hi.compatible pid d p kid hd oldPeer hc d key hd oldKey
  · intro after pid p kid ha hp hc
    have eq : after = keyAllocationDevice d (w.keypairCounter + 1) word :=
      Option.some.inj ha.symm
    subst after
    exact Nat.lt_trans (hi.below d pid p kid hd hp hc) (Nat.lt_succ_self _)

theorem keypairCreateCore_preserves (word : Option PeerId) :
    Preserves Inv (keypairCreateCore word) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  rw [keypairCreateCore_run] at hr
  cases hd : w.dev with
  | none => simp [hd] at hr
  | some d =>
    simp only [hd, Except.ok.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact allocate hi hd word

theorem keypairCreate_preserves (word : Option PeerId) :
    Preserves Inv (keypairCreate word) := by
  rw [keypairCreate_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.hiddenAlloc .kzallocKeypair) Inv)
  intro allocated
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .keypairCreateNoMem !allocated) Inv)
  intro refused
  cases refused with
  | true => exact preserves_pure _
  | false =>
    apply preserves_bind (keypairCreateCore_preserves word)
    intro id
    exact preserves_pure (some id)

/-- A source current-slot transition and monotone allocation frontier suffice;
the allowed replacement's nullable ownership and bound are checked at entry. -/
theorem retain (hi : Inv w) (effect : KeyEffect allowed w v)
    (frontier : ∀ before after, w.dev = some before → v.dev = some after →
      before.nextKeypairId ≤ after.nextKeypairId)
    (incoming : ∀ pid kid, allowed pid kid → KeyCompatible pid kid w ∧
      ∀ d, w.dev = some d → kid < d.nextKeypairId) : Inv v := by
  refine ⟨effect.currentsCompatible hi.compatible (fun p k h => (incoming p k h).1), ?_⟩
  intro after pid p kid ha hp hc
  have cell : currentCells v pid = some (p.internalId, some kid) := by
    simp [currentCells, currentCell, ha, hp, hc]
  obtain ⟨old, ho, changed⟩ := effect.currents pid p.internalId (some kid) cell
  obtain ⟨prior, hprior, fields⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨before, hb, hpeer⟩ := Option.bind_eq_some_iff.mp hprior
  apply Nat.lt_of_lt_of_le _ (frontier before after hb ha)
  rcases changed with same | ⟨k, hk, allowed⟩
  · have current : prior.keypairCurrent = some kid :=
      (congrArg Prod.snd fields).trans same.symm
    exact hi.below before pid prior kid hb hpeer current
  · cases hk
    exact (incoming pid kid allowed).2 before hb

theorem keypairPut_preserves (kp : Option KeypairId) (now : Bool) :
    Preserves Inv (keypairPut kp now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have effect := (KeyEffects.iff_run_ambient _ _).mp
    (keypairPut_keyEffect (allowed := NoPromotion) kp now) w a result v b hr
  have geometry := keypairPut_retention kp now w v a b hr
  apply retain hi effect
  · intro before after hb ha
    obtain ⟨d, hd, fields⟩ := allocationMetadata_device geometry.metadata ha
    have eq : d = before := Option.some.inj (hd.symm.trans hb)
    subst d
    exact Nat.le_of_eq (congrArg DeviceAllocationMetadata.nextKeypair fields).symm
  · intro p k impossible
    cases impossible

/-- The promotion is justified by the actual received key. A packet caller
can supply this key's bound from OwnerBounds.Carrier.rxKeys. -/
theorem receivedWithKeypair_preserves (pid : PeerId) (kid : KeypairId) :
    Hoare (receivedWithKeypair pid kid)
      (fun w => Inv w ∧ KeyCompatible pid kid w ∧
        ∀ d, w.dev = some d → kid < d.nextKeypairId)
      (fun _ => Inv) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have effect := (KeyEffects.iff_run_ambient _ _).mp
    (receivedWithKeypair_keyEffect pid kid) w a result v b hr
  have geometry := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.received_geometry) pid kid)
      w a result v b hr
  apply retain hi.1 effect
  · intro before after hb ha
    have fields := congrArg Prod.fst geometry
    have eq : (after.ifindex, after.nextPeer, after.nextKeypairId) =
        (before.ifindex, before.nextPeer, before.nextKeypairId) := by
      simpa only [OwnerCompletion.geometry, ha, hb, Option.map_some, Option.some.injEq] using fields
    exact Nat.le_of_eq (congrArg (fun x => x.2.2) eq).symm
  · intro p k h
    rcases h with ⟨rfl, rfl⟩
    exact hi.2

private theorem read_preserves (pid : PeerId) : Preserves Inv (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  obtain ⟨rfl, _, _, _, _⟩ := Origins.getPeer_return _ _ _ _ _ _ hr
  exact hi

private theorem update (hi : Inv w) (hd : w.dev = some d)
    (hp : d.peers[pid]? = some old) (p : Peer)
    (subset : ∀ kid, p.keypairCurrent = some kid → old.keypairCurrent = some kid) :
    Inv {w with dev := some {d with peers := d.peers.insert pid p}} := by
  constructor
  · intro q after peer kid ha hpeer hc other key hb hk
    have ea : after = {d with peers := d.peers.insert pid p} := Option.some.inj ha.symm
    have eb : other = after := Option.some.inj (hb.symm.trans ha)
    subst other
    subst after
    by_cases same : pid = q
    · subst q
      have eq : peer = p := by simpa using hpeer.symm
      subst peer
      exact hi.compatible pid d old kid hd hp (subset kid hc) d key hd hk
    · exact hi.compatible q d peer kid hd
        (by simpa [Std.TreeMap.getElem?_insert, same] using hpeer) hc d key hd hk
  · intro after q peer kid ha hpeer hc
    have ea : after = {d with peers := d.peers.insert pid p} := Option.some.inj ha.symm
    subst after
    by_cases same : pid = q
    · subst q
      have eq : peer = p := by simpa using hpeer.symm
      subst peer
      exact hi.below d pid old kid hd hp (subset kid hc)
    · exact hi.below d q peer kid hd
        (by simpa [Std.TreeMap.getElem?_insert, same] using hpeer) hc

private theorem modifyPeer_preserves (pid : PeerId) (f : Peer → Peer)
    (subset : ∀ p kid, (f p).keypairCurrent = some kid → p.keypairCurrent = some kid) :
    Preserves Inv ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  change ((do let p ← getPeer pid; setPeer pid (f p)).run w).run a =
    .ok ((result,v),b) at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p, u, middle, hg, hs⟩ := hr
  obtain ⟨rfl, rfl, d, hd, hp⟩ := Origins.getPeer_return _ _ _ _ _ _ hg
  cases hs
  simpa only [setPeer, modifyDev, hd, Option.map_some] using update hi hd hp (f p) (subset p)

theorem keypairsClear_preserves (pid : PeerId) : Preserves Inv (keypairsClear pid) := by
  unfold keypairsClear
  apply preserves_bind (read_preserves pid)
  intro p
  apply preserves_bind (modifyPeer_preserves pid (fun p => {p with keypairNext := none})
    (fun _ _ h => h))
  intro _
  apply preserves_bind (keypairPut_preserves p.keypairNext true)
  intro _
  apply preserves_bind (read_preserves pid)
  intro p
  apply preserves_bind (modifyPeer_preserves pid (fun p => {p with keypairPrevious := none})
    (fun _ _ h => h))
  intro _
  apply preserves_bind (keypairPut_preserves p.keypairPrevious true)
  intro _
  apply preserves_bind (read_preserves pid)
  intro p
  apply preserves_bind (modifyPeer_preserves pid (fun p => {p with keypairCurrent := none})
    (by intro p kid h; cases h))
  intro _
  exact keypairPut_preserves p.keypairCurrent true

/-- The existing complete affiliation proof supplies actual session rotation,
including allocation refusal and normal false results. Full affiliation is an
explicit local input here, not an established initialized runner invariant. -/
theorem beginSession_establishes (pid : PeerId) :
    Hoare (beginSession pid) Affiliation.Inv (fun _ w => Affiliation.Inv w ∧ Inv w) := by
  exact hoare_consequence (Affiliation.beginSession_affiliation pid)
    (fun _ h => h) (fun _ _ h => ⟨h, of_affiliation h⟩)

theorem addNewKeypair_establishes (pid : PeerId) (kid : KeypairId) :
    Hoare (addNewKeypair pid kid) (fun w => Affiliation.References pid [kid] (Affiliation.view w))
      (fun _ w => Affiliation.Inv w ∧ Inv w) := by
  exact hoare_consequence (Affiliation.addNewKeypair_affiliation pid kid)
    (fun _ h => h) (fun _ _ h => ⟨h, of_affiliation h⟩)

theorem keypairsClear_establishes (pid : PeerId) :
    Hoare (keypairsClear pid) Affiliation.Inv (fun _ w => Affiliation.Inv w ∧ Inv w) := by
  exact hoare_consequence (Affiliation.keypairsClear_affiliation pid)
    (fun _ h => h) (fun _ _ h => ⟨h, of_affiliation h⟩)

def danglingPeer : Peer :=
  {remoteStatic := [], presharedKey := [], precomputedStaticStatic := [],
   internalId := 1, keypairCurrent := some 0}
def danglingDevice : Device :=
  {ifindex := 3, ifname := "wg0", nextPeer := 2,
   peers := ({} : Std.TreeMap PeerId Peer).insert 0 danglingPeer}
def danglingWorld : WGWorld := {dev := some danglingDevice}

theorem dangling_compatible : CurrentsCompatible danglingWorld := by
  intro pid d p kid hd hp hc other key ho hk
  have eq : other = danglingDevice := Option.some.inj ho.symm
  subst other
  simp [danglingDevice] at hk

theorem dangling_ownerCarrier : OwnerBounds.Carrier danglingWorld := by
  constructor
  · intro d hd slot key hk
    have eq : d = danglingDevice := Option.some.inj hd.symm
    subst d
    simp [danglingDevice] at hk
  · intro d id pkt hd hp
    have eq : d = danglingDevice := Option.some.inj hd.symm
    subst d
    simp [danglingDevice] at hp
  · intro d hd id pkt hp
    have eq : d = danglingDevice := Option.some.inj hd.symm
    subst d
    simp [danglingDevice] at hp

theorem dangling_not_below : ¬ Below danglingWorld := by
  intro h
  have impossible := h danglingDevice 0 danglingPeer 0 rfl
    (by simp [danglingDevice]) rfl
  exact Nat.not_lt_zero _ impossible

theorem allocation_breaks_unbounded_current :
    ¬ CurrentsCompatible (keyAllocationWorld danglingWorld danglingDevice (some 1)) := by
  intro hc
  have bad := hc 0 (keyAllocationDevice danglingDevice 1 (some 1)) danglingPeer 0 rfl
    (by simp [keyAllocationDevice, danglingDevice]) rfl
    (keyAllocationDevice danglingDevice 1 (some 1))
    ({internalId := 1, peer := some 1} : Keypair) rfl
    (by simp [keyAllocationDevice, danglingDevice])
  simp [Affiliation.Compatible] at bad

theorem actual_core_counterexample (ambient : Ambient) :
    ∃ v, ((keypairCreateCore (some 1)).run danglingWorld).run ambient = .ok ((0,v),ambient) ∧
      OwnerBounds.Carrier danglingWorld ∧ CurrentsCompatible danglingWorld ∧
      ¬ CurrentsCompatible v := by
  exact ⟨keyAllocationWorld danglingWorld danglingDevice (some 1),
    keypairCreateCore_run _ _ _, dangling_ownerCarrier, dangling_compatible,
    allocation_breaks_unbounded_current⟩

end Leanux.Proofs.WG.CurrentKeys
