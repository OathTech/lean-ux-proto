import Leanux.Proofs.WG.Noise.SlotFrames

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem getPeer_exact_spec (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜peerAt w pid = some p⌝⦄ getPeer pid
    ⦃⇓? r w => ⌜r = p ∧ peerAt w pid = some p⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient r g' ambient' hp hr
  obtain ⟨hp', found⟩ := (ensures_iff _ _ _).mpr
    (getPeer_spec pid (fun g => peerAt g pid = some p)) g ambient r g' ambient' hp hr
  exact ⟨Option.some.inj (found.symm.trans hp'), hp'⟩

theorem modifyPeer_exact_spec (pid : PeerId) (f : Peer → Peer) (p : Peer) :
    ⦃fun w => ⌜peerAt w pid = some p⌝⦄ modifyPeer pid f
    ⦃⇓? _ w => ⌜peerAt w pid = some (f p)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  change Ensures (getPeer pid >>= fun p => setPeer pid (f p)) _ _
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_exact_spec pid p)) ?_
  intro found g ambient result g' ambient' hp hr
  rcases hp with ⟨rfl, hp⟩
  change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
    {d with peers := d.peers.insert pid (f found)})}), ambient) = _ at hr
  cases hr
  cases hd : g.dev with
  | none => simp [peerAt, hd] at hp
  | some d => simp [peerAt]

def clearOne (pid : PeerId) (pick : Peer → Option KeypairId) (clear : Peer → Peer) : WG.M Unit := do
  let old := pick (← getPeer pid)
  modifyPeer pid clear
  keypairPut old true

theorem clearOne_peer (pid : PeerId) (pick : Peer → Option KeypairId)
    (clear : Peer → Peer) (p : Peer) :
    Ensures (clearOne pid pick clear) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some (clear p)) := by
  unfold clearOne
  refine ensures_bind (Q := fun _ g => peerAt g pid = some p) _ _ ?_ ?_
  · intro g ambient found g' ambient' hp hr
    exact ((ensures_iff _ _ _).mpr (getPeer_exact_spec pid p)
      g ambient found g' ambient' hp hr).2
  · intro found
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (modifyPeer_exact_spec pid clear p)) ?_
    intro _
    exact (ensures_iff _ _ _).mpr
      (keypairPut_peers_spec (fun ps => ps pid = some (clear p)) (pick found) true)

theorem keypairsClear_source (pid : PeerId) :
    keypairsClear pid = (do
      clearOne pid Peer.keypairNext (fun p => { p with keypairNext := none })
      clearOne pid Peer.keypairPrevious (fun p => { p with keypairPrevious := none })
      clearOne pid Peer.keypairCurrent (fun p => { p with keypairCurrent := none })) := by
  simp only [keypairsClear, clearOne, bind_assoc]

theorem keypairsClear_peer (pid : PeerId) (p : Peer) :
    Ensures (keypairsClear pid) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some { p with
        keypairNext := none, keypairPrevious := none, keypairCurrent := none }) := by
  rw [keypairsClear_source]
  exact ensures_bind _ _ (clearOne_peer pid _ _ p) fun _ =>
    ensures_bind _ _ (clearOne_peer pid _ _ { p with keypairNext := none }) fun _ =>
      clearOne_peer pid _ _ { p with keypairNext := none, keypairPrevious := none }

theorem keypairsClear_slots (pid : PeerId) (p : Peer) :
    Ensures (keypairsClear pid) (fun w => peerAt w pid = some p)
      (fun _ w => ∃ p', peerAt w pid = some p' ∧ slots p' = ⟨none, none, none⟩) := by
  intro g ambient x g' ambient' hp hr
  exact ⟨_, keypairsClear_peer pid p g ambient x g' ambient' hp hr, rfl⟩

theorem handshakeZero_peer (pid : PeerId) (p : Peer) :
    Ensures (handshakeZero pid)
      (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some { p with
        ephemeralPrivate := List.replicate 32 0,
        remoteEphemeral := List.replicate 32 0,
        hash := List.replicate 32 0,
        chainingKey := List.replicate 32 0,
        remoteIndex := 0, handshakeState := 0 }) := by
  exact (ensures_iff _ _ _).mpr (modifyPeer_exact_spec pid _ p)

theorem receivedWithKeypair_slots (pid : PeerId) (received : KeypairId) (p : Peer) :
    Ensures (receivedWithKeypair pid received)
      (fun w => peerAt w pid = some p)
      (fun ok w => ∃ p', peerAt w pid = some p' ∧
        (ok, slots p') = confirm (slots p) received) := by
  have hread {α : Type} (initial : Peer) (f : Peer → WG.M α)
      (R : α → WGWorld → Prop)
      (hf : Ensures (f initial) (fun g => peerAt g pid = some initial) R) :
      Ensures (getPeer pid >>= f) (fun g => peerAt g pid = some initial) R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_exact_spec pid initial)) ?_
    intro found g ambient x g' ambient' hp hr
    rcases hp with ⟨rfl, hp⟩
    exact hf g ambient x g' ambient' hp hr
  have hbranch {α : Type} (site : Decision) (value : Bool) (f : Bool → WG.M α)
      (P : WGWorld → Prop) (R : α → WGWorld → Prop)
      (hf : Ensures (f value) P R) :
      Ensures ((branch site value : WG.M Bool) >>= f) P R := by
    refine ensures_bind (Q := fun r g => r = value ∧ P g) _ _ ?_ ?_
    · intro g ambient r g' ambient' hp hr
      simp [branch, AmbientM.branch] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, hp⟩
    · intro found g ambient x g' ambient' hp hr
      rcases hp with ⟨rfl, hp⟩
      exact hf g ambient x g' ambient' hp hr
  unfold receivedWithKeypair
  refine hread p _ _ ?_
  refine hbranch _ _ _ _ _ ?_
  by_cases same : p.keypairNext = some received
  · simp only [same, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine hread p _ _ ?_
    refine hbranch _ _ _ _ _ ?_
    simp only [same, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine hread p _ _ ?_
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (modifyPeer_exact_spec pid (fun p => {p with keypairPrevious := p.keypairCurrent}) p)) ?_
    intro _
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (keypairPut_peers_spec
        (fun ps => ps pid = some {p with keypairPrevious := p.keypairCurrent}) p.keypairPrevious true)) ?_
    intro _
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (modifyPeer_exact_spec pid
        (fun p => {p with keypairCurrent := some received, keypairNext := none})
        {p with keypairPrevious := p.keypairCurrent})) ?_
    intro _
    intro g ambient result g' ambient' hp hr
    cases hr
    exact ⟨_, hp, by simp [confirm, slots, same]⟩
  · simp only [bne, beq_eq_false_iff_ne.mpr same, Bool.not_false, ↓reduceIte]
    intro g ambient result g' ambient' hp hr
    cases hr
    exact ⟨p, hp, by simp [confirm, slots, same]⟩

theorem addNewKeypair_slots (pid : PeerId) (newKey : KeypairId)
    (p : Peer) (k : Keypair) :
    Ensures (addNewKeypair pid newKey)
      (fun w => peerAt w pid = some p ∧
        (w.dev.bind fun d => d.keypairs[newKey]?) = some k)
      (fun _ w => ∃ p', peerAt w pid = some p' ∧
        slots p' = rotate (slots p) k.iAmTheInitiator newKey) := by
  let P : WGWorld → Prop := fun g => peerAt g pid = some p ∧
    (g.dev.bind fun d => d.keypairs[newKey]?) = some k
  let R : Unit → WGWorld → Prop := fun _ g => ∃ p', peerAt g pid = some p' ∧
    slots p' = rotate (slots p) k.iAmTheInitiator newKey
  have hpeer (f : Peer → WG.M Unit) (hf : Ensures (f p) P R) :
      Ensures (getPeer pid >>= f) P R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro found g ambient x g' ambient' hp hr
    have eq : found = p := Option.some.inj (hp.2.symm.trans hp.1.1)
    subst found
    exact hf g ambient x g' ambient' hp.1 hr
  have hkey (f : Keypair → WG.M Unit)
      (hf : Ensures (f k) (fun g => peerAt g pid = some p) R) :
      Ensures (getKeypair newKey >>= f) P R := by
    refine ensures_bind (Q := fun key g => key = k ∧ peerAt g pid = some p) _ _ ?_ ?_
    · intro g ambient found g' ambient' hp hr
      cases hd : g.dev with
      | none => simp [P, hd] at hp
      | some d =>
        have hk : d.keypairs[newKey]? = some k := by simpa [P, hd] using hp.2
        simp [getKeypair, getDev, hd, hk] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨rfl, hp.1⟩
    · intro found g ambient x g' ambient' hp hr
      rcases hp with ⟨rfl, hp⟩
      exact hf g ambient x g' ambient' hp hr
  have hbranch {α : Type} (site : Decision) (value : Bool) (f : Bool → WG.M α)
      (P : WGWorld → Prop) (R : α → WGWorld → Prop)
      (hf : Ensures (f value) P R) :
      Ensures ((branch site value : WG.M Bool) >>= f) P R := by
    refine ensures_bind (Q := fun r g => r = value ∧ P g) _ _ ?_ ?_
    · intro g ambient r g' ambient' hp hr
      simp [branch, AmbientM.branch] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, hp⟩
    · intro found g ambient x g' ambient' hp hr
      rcases hp with ⟨rfl, hp⟩
      exact hf g ambient x g' ambient' hp hr
  have hput (initial : Peer) (key : Option KeypairId) :
      Ensures (keypairPut key true) (fun g => peerAt g pid = some initial)
        (fun _ g => peerAt g pid = some initial) :=
    (ensures_iff _ _ _).mpr (keypairPut_peers_spec (fun ps => ps pid = some initial) key true)
  have hfinish (initial : Peer)
      (shape : slots {initial with keypairCurrent := some newKey} =
        rotate (slots p) k.iAmTheInitiator newKey) :
      Ensures (modifyPeer pid (fun q => {q with keypairCurrent := some newKey}))
        (fun g => peerAt g pid = some initial) R := by
    intro g ambient x g' ambient' hp hr
    exact ⟨_, (ensures_iff _ _ _).mpr
      (modifyPeer_exact_spec pid _ initial) g ambient x g' ambient' hp hr, shape⟩
  unfold addNewKeypair
  refine hpeer _ ?_
  refine hkey _ ?_
  refine hbranch _ _ _ _ _ ?_
  cases hi : k.iAmTheInitiator with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (modifyPeer_exact_spec pid (fun q => {q with keypairNext := some newKey}) p)) ?_
    intro _
    refine ensures_bind _ _ (hput _ _) ?_
    intro _
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (modifyPeer_exact_spec pid (fun q => {q with keypairPrevious := none})
        {p with keypairNext := some newKey})) ?_
    intro _
    intro g ambient result g' ambient' hp hr
    exact ⟨_, hput _ _ g ambient result g' ambient' hp hr, by simp [rotate, slots, hi]⟩
  | true =>
    simp only [↓reduceIte]
    refine hbranch _ _ _ _ _ ?_
    cases hn : p.keypairNext with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (modifyPeer_exact_spec pid (fun q => {q with keypairPrevious := p.keypairCurrent}) p)) ?_
      intro _
      refine ensures_bind _ _ (hput _ _) ?_
      intro _
      exact hfinish _ (by simp [rotate, slots, hi, hn])
    | some next =>
      simp only [Option.isSome_some, ↓reduceIte]
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (modifyPeer_exact_spec pid (fun q => {q with keypairNext := none, keypairPrevious := some next}) p)) ?_
      intro _
      refine ensures_bind _ _ (hput _ _) ?_
      intro _
      refine ensures_bind _ _ (hput _ _) ?_
      intro _
      exact hfinish _ (by simp [rotate, slots, hi, hn])

end Leanux.Proofs.WG.Noise
