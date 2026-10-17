import Leanux.Proofs.WG.Noise.AccessSource
import Leanux.Proofs.WG.Noise.ComponentFrames

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

abbrev unhashEntry := noise_const _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry
abbrev modifyPeer := noise_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer

theorem modifyDev_peers_spec (P : (PeerId → Option Peer) → Prop)
    (f : Device → Device) (hf : ∀ d, (f d).peers = d.peers) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result g' ambient' hp hr
  change Except.ok (((), {g with dev := g.dev.map f}), ambient) = _ at hr
  cases hr
  have he : peerAt {g with dev := g.dev.map f} = peerAt g := by
    funext pid
    simp [peerAt, Option.bind_map, Function.comp_def, hf]
  exact he ▸ hp

theorem keypairPut_peers_spec (P : (PeerId → Option Peer) → Prop)
    (kp : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ keypairPut kp now
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  let Q : WGWorld → Prop := fun g => P (peerAt g)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) Q (fun _ => Q) := by
    intro g ambient y g' ambient' hp hr
    cases hr
    exact hp
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) Q (fun _ => Q) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) Q)
  have hread (id : KeypairId) : Ensures (getKeypair id) Q (fun _ => Q) := by
    intro g ambient k g' ambient' hp hr
    cases hd : g.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[id]? with
      | none =>
        simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
        cases hr
      | some k =>
        simp [getKeypair, getDev, hd, hk] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hp
  have hderef (id : KeypairId) :
      Ensures (IndexOwner.peerDeref (.keypair id)) Q (fun _ => Q) := by
    unfold IndexOwner.peerDeref IndexOwner.peerWord
    refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
    · refine ensures_bind (Q := fun _ => Q) _ _ (hread id) ?_
      intro key
      exact hpure key.peer
    · intro word
      cases word with
      | none =>
        exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
          (AmbientM.unsupported "entry->peer is NULL: the C dereferences it") Q)
      | some pid => exact hpure pid
  have hindex (id : KeypairId) :
      Ensures (liftIndex (indexRemove (.keypair id))) Q (fun _ => Q) := by
    refine (ensures_iff _ _ _).mpr (hoare_liftIndex_variant _ Q ?_)
    intro g d table hp hd
    have he : peerAt {g with dev := some {d with indexTable := table}} = peerAt g := by
      funext pid
      simp [peerAt, hd]
    dsimp only [Q]
    rw [he]
    exact hp
  have hremove (id : KeypairId) : Ensures (do
      let _ ← IndexOwner.peerDeref (.keypair id)
      liftIndex (indexRemove (.keypair id))) Q (fun _ => Q) :=
    ensures_bind _ _ (hderef id) (fun _ => hindex id)
  have href (old : Nat) :
      Ensures (refcountDecAndTest old : WG.M Bool) Q (fun _ => Q) := by
    intro g ambient result g' ambient' hp hr
    cases old with
    | zero =>
      simp [refcountDecAndTest, branchCmp, AmbientM.branchCmp,
        branch, AmbientM.branch, unsupported, AmbientM.unsupported] at hr
      cases hr
    | succ n =>
      cases n with
      | zero =>
        simp [refcountDecAndTest, branchCmp, AmbientM.branchCmp] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hp
      | succ n =>
        simp [refcountDecAndTest, branchCmp, AmbientM.branchCmp, branch, AmbientM.branch] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hp
  apply (ensures_iff _ _ _).mp
  unfold keypairPut
  refine ensures_bind (Q := fun _ => Q) _ _ (hbranch _ _) ?_
  intro null
  cases kp with
  | none =>
    cases null with
    | true => exact hpure ()
    | false =>
      exact (ensures_iff _ _ _).mpr
        (hoare_liftAmbient_variant (AmbientM.invariant "unreachable") Q)
  | some id =>
    cases null with
    | true => exact hpure ()
    | false =>
      refine ensures_bind (Q := fun _ => Q) _ _ (hread id) ?_
      intro key
      refine ensures_bind (Q := fun _ => Q) _ _ (hbranch _ _) ?_
      intro removeNow
      have htail : Ensures (do
          setKeypair id {key with refcount := key.refcount - 1}
          if ← branch .keypairKrefPutReleased (← refcountDecAndTest key.refcount) then
            (do
              let _ ← IndexOwner.peerDeref (.keypair id)
              liftIndex (indexRemove (.keypair id)))
            modifyDev fun d => {d with keypairs := d.keypairs.erase id}) Q (fun _ => Q) := by
        refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
        · exact (ensures_iff _ _ _).mpr (modifyDev_peers_spec P _ (fun _ => rfl))
        · intro _
          refine ensures_bind (Q := fun _ => Q) _ _ (href _) ?_
          intro released
          refine ensures_bind (Q := fun _ => Q) _ _ (hbranch _ _) ?_
          intro b
          cases b with
          | false => exact hpure ()
          | true =>
            refine ensures_bind (Q := fun _ => Q) _ _ (hremove id) ?_
            intro _
            exact (ensures_iff _ _ _).mpr (modifyDev_peers_spec P _ (fun _ => rfl))
      cases removeNow with
      | false => exact htail
      | true =>
        refine ensures_bind (Q := fun _ => Q) _ _ (hremove id) ?_
        intro _
        exact htail

def tagAt (g : WGWorld) (pid : PeerId) : Option Nat :=
  (peerAt g pid).map Peer.handshakeState

theorem addNewKeypair_tag_spec (pid : PeerId) (kp : KeypairId) (tag : Nat) :
    ⦃fun w => ⌜tagAt w pid = some tag⌝⦄ addNewKeypair pid kp
    ⦃⇓? _ w => ⌜tagAt w pid = some tag⌝⦄ := by
  let Q : WGWorld → Prop := fun g => tagAt g pid = some tag
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) Q (fun _ => Q) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) Q)
  have hpeer : Ensures (getPeer pid) Q (fun _ => Q) := by
    intro g ambient p g' ambient' hp hr
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid Q) g ambient p g' ambient' hp hr).1
  have hread (id : KeypairId) : Ensures (getKeypair id) Q (fun _ => Q) := by
    intro g ambient k g' ambient' hp hr
    cases hd : g.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[id]? with
      | none =>
        simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
        cases hr
      | some k =>
        simp [getKeypair, getDev, hd, hk] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hp
  have hput (key : Option KeypairId) :
      Ensures (keypairPut key true) Q (fun _ => Q) :=
    (ensures_iff _ _ _).mpr
      (keypairPut_peers_spec (fun ps => (ps pid).map Peer.handshakeState = some tag) key true)
  have hmodify (f : Peer → Peer) (hf : ∀ p, (f p).handshakeState = p.handshakeState) :
      Ensures ((noise_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f)
        Q (fun _ => Q) := by
    change Ensures (getPeer pid >>= fun p => setPeer pid (f p)) Q (fun _ => Q)
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid Q)) ?_
    intro p g ambient result g' ambient' hp hr
    change Except.ok (((), {g with dev := g.dev.map (fun d : Device => {d with peers := d.peers.insert pid (f p)})}), ambient) = _ at hr
    cases hr
    have ptag : p.handshakeState = tag := by
      simpa [Q, tagAt, hp.2] using hp.1
    cases hd : g.dev with
    | none => simp [peerAt, hd] at hp
    | some d => simp [Q, tagAt, peerAt, hf, ptag]
  apply (ensures_iff _ _ _).mp
  unfold addNewKeypair
  refine ensures_bind (Q := fun _ => Q) _ _ hpeer ?_
  intro p
  refine ensures_bind (Q := fun _ => Q) _ _ (hread kp) ?_
  intro key
  refine ensures_bind (Q := fun _ => Q) _ _ (hbranch _ _) ?_
  intro initiator
  cases initiator with
  | false =>
    refine ensures_bind (Q := fun _ => Q) _ _ (hmodify _ (fun _ => rfl)) ?_
    intro _
    refine ensures_bind (Q := fun _ => Q) _ _ (hput _) ?_
    intro _
    refine ensures_bind (Q := fun _ => Q) _ _ (hmodify _ (fun _ => rfl)) ?_
    intro _
    exact hput _
  | true =>
    refine ensures_bind (Q := fun _ => Q) _ _ (hbranch _ _) ?_
    intro hasNext
    have tail : Ensures (do
        keypairPut p.keypairPrevious true
        (noise_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
          (fun p => {p with keypairCurrent := some kp})) Q (fun _ => Q) := by
      refine ensures_bind (Q := fun _ => Q) _ _ (hput _) ?_
      intro _
      exact hmodify _ (fun _ => rfl)
    cases hasNext with
    | false =>
      refine ensures_bind (Q := fun _ => Q) _ _ (hmodify _ (fun _ => rfl)) ?_
      intro _
      exact tail
    | true =>
      refine ensures_bind (Q := fun _ => Q) _ _ (hmodify _ (fun _ => rfl)) ?_
      intro _
      refine ensures_bind (Q := fun _ => Q) _ _ (hput _) ?_
      intro _
      exact tail

end Leanux.Proofs.WG.Noise
