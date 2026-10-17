import Leanux.Proofs.WG.Origins.CurrentPeerCreation
import Leanux.Proofs.WG.Queues.AffiliationCompatibility
import Leanux.Proofs.WG.Peers.AffiliationMaintenance

/-! Owner and RX-reference bounds for receiving identity and peer creation.
This carrier does not establish the TX/current-slot compatibility of full
affiliation. The supplied-state allocation witness below is not an initialized
execution or an R3 counterexample. -/
namespace Leanux.Proofs.WG.OwnerBounds
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues.RxCredits Std.Do

def RxKeysBelow (w : WGWorld) : Prop :=
  ∀ d, w.dev = some d → ∀ (id : SkbId) (pkt : RxPacket), d.rxSkbs[id]? = some pkt →
    pkt.keypair < d.nextKeypairId

structure Carrier (w : WGWorld) : Prop where
  owners : CurrentIdentity.ReceivingOwnersBelow w
  compatible : RxCompatible w
  rxKeys : RxKeysBelow w

theorem of_affiliation (hi : Affiliation.Inv w) : Carrier w := by
  refine ⟨CurrentIdentity.receivingOwnersBelow_of_affiliation hi,
    rxCompatible_of_affiliation hi, ?_⟩
  intro d hd id pkt hp
  have inv := hi (Affiliation.state d) (by simp [Affiliation.view, hd])
  exact (inv.rx id pkt.peer pkt.keypair (by simp [Affiliation.state, hp])).2.1

theorem initial (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) : Carrier w :=
  of_affiliation (Affiliation.initial net bare w hw)

theorem owners_retain (hi : CurrentIdentity.ReceivingOwnersBelow w)
    (hr : Origins.Retains w v)
    (frontier : ∀ before after, w.dev = some before → v.dev = some after →
      before.ifindex = after.ifindex → before.nextPeer ≤ after.nextPeer) :
    CurrentIdentity.ReceivingOwnersBelow v := by
  intro after ha slot key hk valid pid word
  obtain ⟨keys, old, hw, ho, vo, le⟩ := hr after.ifindex
    (fun i => after.keypairs[i]?) (by simp [Origins.view, ha]) slot key hk valid
  obtain ⟨before, hb, fields⟩ := Option.map_eq_some_iff.mp hw
  have epoch := congrArg Prod.fst fields
  have cells := congrFun (congrArg Prod.snd fields) slot
  have oldWord : old.peer = some pid := Origins.WordLe.some (word ▸ le.2)
  exact Nat.lt_of_lt_of_le (hi before hb slot old (cells.trans ho) vo pid oldWord)
    (frontier before after hb ha epoch)

theorem configured_word_below {d : Device} {pid owner : PeerId} {p : Peer}
    (hi : ConfiguredIdentity.Inv w)
    (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (word : p.handshakeEntryPeer = some owner) : owner < d.nextPeer := by
  have inv := hi (ConfiguredIdentity.state d) (by simp [ConfiguredIdentity.view, hd])
  have resident : (ConfiguredIdentity.state d).peers pid = some (ConfiguredIdentity.cell p) := by
    simp [ConfiguredIdentity.state, hp]
  have self := inv.self pid (ConfiguredIdentity.cell p) resident
  rcases self with null | self
  · simp [ConfiguredIdentity.cell, word] at null
  · have same : owner = pid := Option.some.inj (word.symm.trans self)
    subst owner
    exact inv.bounded _ _ resident

theorem allocate (hi : Carrier w) (hd : w.dev = some d) (word : Option PeerId) :
    Carrier (keyAllocationWorld w d word) := by
  constructor
  · intro after ha slot key hk valid pid owner
    have eq : after = keyAllocationDevice d (w.keypairCounter + 1) word :=
      Option.some.inj ha.symm
    subst after
    by_cases atSlot : d.nextKeypairId = slot
    · subst slot
      simp only [keyAllocationDevice, Std.TreeMap.getElem?_insert_self, Option.some.injEq] at hk
      subst key
      cases valid
    · have old : d.keypairs[slot]? = some key := by
        simpa [keyAllocationDevice, Std.TreeMap.getElem?_insert, atSlot] using hk
      exact hi.owners d hd slot key old valid pid owner
  · intro after id pkt ha hp other key hb hk
    have ea : after = keyAllocationDevice d (w.keypairCounter + 1) word := Option.some.inj ha.symm
    have eb : other = after := Option.some.inj (hb.symm.trans ha)
    subst other
    subst after
    have resident : d.rxSkbs[id]? = some pkt := hp
    have below := hi.rxKeys d hd id pkt resident
    have old : d.keypairs[pkt.keypair]? = some key := by
      simpa [keyAllocationDevice, Std.TreeMap.getElem?_insert,
        Ne.symm (Nat.ne_of_lt below)] using hk
    exact hi.compatible d id pkt hd resident d key hd old
  · intro after ha id pkt hp
    have eq : after = keyAllocationDevice d (w.keypairCounter + 1) word := Option.some.inj ha.symm
    subst after
    exact Nat.lt_trans (hi.rxKeys d hd id pkt hp) (Nat.lt_succ_self _)

theorem keypairCreateCore_preserves (word : Option PeerId) :
    Preserves Carrier (keypairCreateCore word) := by
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
    Preserves Carrier (keypairCreate word) := by
  rw [keypairCreate_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.hiddenAlloc .kzallocKeypair) Carrier)
  intro allocated
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .keypairCreateNoMem !allocated) Carrier)
  intro refused
  cases refused with
  | true => exact preserves_pure _
  | false =>
    apply preserves_bind (keypairCreateCore_preserves word)
    intro id
    exact preserves_pure (some id)

def danglingPacket : RxPacket :=
  {peer := 0, keypair := 0, bytes := [], source := ⟨4, 0, 0, 0, 0, 0⟩}

def danglingDevice : Device :=
  {ifindex := 3, ifname := "wg0", nextPeer := 2,
   rxSkbs := ({} : Std.TreeMap SkbId RxPacket).insert 0 danglingPacket}

def danglingWorld : WGWorld := {dev := some danglingDevice}

theorem dangling_compatible : RxCompatible danglingWorld := by
  intro d id pkt hd hp other key ho hk
  have eq : other = danglingDevice := Option.some.inj ho.symm
  subst other
  simp [danglingDevice] at hk

theorem dangling_owner_bound : CurrentIdentity.ReceivingOwnersBelow danglingWorld := by
  intro d hd slot key hk
  have eq : d = danglingDevice := Option.some.inj hd.symm
  subst d
  simp [danglingDevice] at hk

theorem allocation_breaks_unbounded_compatibility :
    ¬ RxCompatible (keyAllocationWorld danglingWorld danglingDevice (some 1)) := by
  intro hc
  have bad := hc (keyAllocationDevice danglingDevice 1 (some 1)) 0 danglingPacket rfl
    (by simp [keyAllocationDevice, danglingDevice])
    (keyAllocationDevice danglingDevice 1 (some 1))
    ({internalId := 1, peer := some 1} : Keypair) rfl
    (by simp [keyAllocationDevice, danglingDevice, danglingPacket])
  simp [Affiliation.Compatible, danglingPacket] at bad

theorem actual_core_counterexample (ambient : Ambient) :
    ∃ v, ((keypairCreateCore (some 1)).run danglingWorld).run ambient =
        .ok ((0, v), ambient) ∧
      RxCompatible danglingWorld ∧ CurrentIdentity.ReceivingOwnersBelow danglingWorld ∧
      ¬ RxCompatible v := by
  refine ⟨keyAllocationWorld danglingWorld danglingDevice (some 1), ?_,
    dangling_compatible, dangling_owner_bound, allocation_breaks_unbounded_compatibility⟩
  exact keypairCreateCore_run _ _ _

end Leanux.Proofs.WG.OwnerBounds
