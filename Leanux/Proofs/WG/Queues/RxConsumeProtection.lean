import Leanux.Proofs.WG.Queues.TxRxProtection

/-! The RX callback's compatibility facts concern nullable owner words even
when receiving material is invalid. They do not assert initialized affiliation. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option pp.structureInstances false

def compatibleState (pid : PeerId) (kid : KeypairId) (s : Option Affiliation.State) : Prop :=
  ∀ t stamp word, s = some t → t.keys kid = some (stamp,word) → Affiliation.Compatible word pid

theorem compatible_factor : KeyCompatible pid kid w ↔ compatibleState pid kid (Affiliation.view w) := by
  constructor
  · intro h t stamp word hv hk
    obtain ⟨d,hd,rfl⟩ := Option.map_eq_some_iff.mp hv
    change d.keypairs[kid]?.map Affiliation.keyCell = some (stamp,word) at hk
    obtain ⟨k,hslot,hcell⟩ := Option.map_eq_some_iff.mp hk
    have hp := h d k hd hslot
    have hw : k.peer = word := congrArg Prod.snd hcell
    simpa only [hw] using hp
  · intro h d k hd hk
    exact h (Affiliation.state d) k.internalId k.peer
      (by simp [Affiliation.view,hd]) (by simp [Affiliation.state,Affiliation.keyCell,hk])

theorem compatible_erase (pid kid : Nat) (s : Affiliation.State) (other : KeypairId)
    (h : compatibleState pid kid (some s)) : compatibleState pid kid (some (s.eraseKey other)) := by
  intro t stamp word ht hk
  cases ht
  by_cases he : kid = other
  · simp [Affiliation.State.eraseKey,he] at hk
  · exact h s stamp word rfl (by simpa [Affiliation.State.eraseKey,he] using hk)

theorem keypairPut_compatible (pid kid : Nat) (old : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ keypairPut old now
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  simpa only [compatible_factor] using Affiliation.keypairPut_affiliation
    (compatibleState pid kid) (compatible_erase pid kid) old now

theorem setPeer_compatible (pid kid target : Nat) (p : Peer) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ setPeer target p
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  unfold setPeer modifyDev
  apply hoare_modify
  intro w h
  intro d k hd hk
  cases hw : w.dev with
  | none => simp [hw] at hd
  | some old =>
    simp [hw] at hd
    subst d
    exact h old k hw hk

theorem modifyPeer_compatible (pid kid target : Nat) (f : Peer → Peer) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) target f)
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  change ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ (do let p ← getPeer target; setPeer target (f p))
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄
  apply preserves_bind
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' h hr
    obtain ⟨rfl,_,_,_,_⟩ := getPeer_normal target w v p ambient ambient' hr
    exact h
  · intro p
    exact setPeer_compatible pid kid target (f p)

theorem receivedWithKeypair_compatible (pid kid : Nat) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ receivedWithKeypair pid kid
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  let P := KeyCompatible pid kid
  have getter (target : PeerId) : Preserves P (getPeer target) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' h hr
    obtain ⟨rfl,_,_,_,_⟩ := getPeer_normal target w v p ambient ambient' hr
    exact h
  have hk := fun old => keypairPut_compatible pid kid old true
  have hm := modifyPeer_compatible pid kid pid
  change Preserves P (receivedWithKeypair pid kid)
  unfold receivedWithKeypair
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact getter _)
    | (index_material_head keypairPut; exact hk _)
    | (index_material_head modifyPeer; exact hm _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

theorem receivedWithKeypair_protect (pid kid : Nat) : SameView protectView (receivedWithKeypair pid kid) := by
  intro initial
  let P : WGWorld → Prop := fun w => protectView w = initial
  have getter (target : PeerId) : Preserves P (getPeer target) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' h hr
    obtain ⟨rfl,_,_,_,_⟩ := getPeer_normal target w v p ambient ambient' hr
    exact h
  have hk := fun old => (keypairPut_protect old true).wp (fun t => t = initial)
  have hm := fun f hf => (modifyPeer_protect pid f hf).wp (fun t => t = initial)
  change Preserves P (receivedWithKeypair pid kid)
  unfold receivedWithKeypair
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact getter _)
    | (index_material_head keypairPut; exact hk _)
    | (index_material_head modifyPeer; exact hm _ (fun _ => rfl))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

def CurrentIs (pid kid : Nat) (w : WGWorld) : Prop :=
  ∀ d p, w.dev = some d → d.peers[pid]? = some p → p.keypairCurrent = some kid

theorem any_normal {S : Type} (a : StateT S (Except Stop) α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_run _ _ _).mpr
  exact fun _ _ _ _ _ => True.intro

theorem install_current (pid kid : Nat) :
    ⦃fun _ => ⌜True⌝⦄ ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
      (fun p => {p with keypairCurrent := some kid, keypairNext := none}))
    ⦃⇓? _ w => ⌜CurrentIs pid kid w⌝⦄ := by
  change ⦃fun _ => ⌜True⌝⦄ (do let p ← getPeer pid; setPeer pid {p with keypairCurrent := some kid,keypairNext := none})
    ⦃⇓? _ w => ⌜CurrentIs pid kid w⌝⦄
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' _ hr
  obtain ⟨p,a,midway,hget,hset⟩ := bind_ok_native hr
  obtain ⟨rfl,_,d,hd,_⟩ := getPeer_normal pid w a p ambient midway hget
  cases hset
  intro dev peer hdev hpeer
  simp only [hd,Option.map_some,Option.some.injEq] at hdev
  subst dev
  simp only [Std.TreeMap.getElem?_insert_self,Option.some.injEq] at hpeer
  subst peer
  rfl

theorem receivedWithKeypair_current (pid kid : Nat) :
    ⦃fun _ => ⌜True⌝⦄ receivedWithKeypair pid kid
    ⦃⇓? result w => ⌜result = true → CurrentIs pid kid w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' _ hr ht
  subst result
  simp only [receivedWithKeypair,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,a,aa,hget,notNew,b,ab,hfirst,hr⟩ := hr
  cases notNew with
  | true => simp at hr
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨q,c,ac,hget2,changed,e,ae,hsecond,hr⟩ := hr
    cases changed with
    | true => simp at hr
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
      obtain ⟨old,f,af,hget3,u,g,ag,hprev,u,h,ah,hput,u,j,aj,hinstall,hr⟩ := hr
      cases hr
      exact (hoare_iff_run_ambient _ _ _).mp (install_current pid kid) h ah u _ _ True.intro hinstall

/-- Promotion of this packet's key derives the staged-send precondition.
Erasure of an aliased old key is permitted; no receiving-validity premise. -/
theorem receivedWithKeypair_current_compatible (hc : KeyCompatible pid kid w)
    (ambient ambient' : Ambient)
    (hr : ((receivedWithKeypair pid kid).run w).run ambient = .ok ((true,v),ambient')) :
    CurrentCompatible pid v := by
  have same := (hoare_iff_run_ambient _ _ _).mp
    (receivedWithKeypair_compatible pid kid) w ambient true v ambient' hc hr
  have current := (hoare_iff_run_ambient _ _ _).mp
    (receivedWithKeypair_current pid kid) w ambient true v ambient' True.intro hr rfl
  intro d p selected hd hp hs
  have eq := (current d p hd hp).symm.trans hs
  have he : kid = selected := Option.some.inj eq
  subst selected
  exact same

def keyWords (w : WGWorld) : KeypairId → Option (Option PeerId) :=
  fun kid => (w.dev.bind fun d => d.keypairs[kid]?).map (·.peer)

theorem compatible_words : KeyCompatible pid kid w ↔
    ∀ word, keyWords w kid = some word → Affiliation.Compatible word pid := by
  constructor
  · intro h word hw
    obtain ⟨k,hk,rfl⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨d,hd,hslot⟩ := Option.bind_eq_some_iff.mp hk
    exact h d k hd hslot
  · intro h d k hd hk
    exact h k.peer (by simp [keyWords,hd,hk])

theorem keyWords_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => keyWords (project w)) a :=
  ha.of_factor (fun store : WGStoreView => fun kid =>
    (store.dev.bind fun d => d.keypairs[kid]?).map (·.peer)) _ (fun _ => rfl)

theorem modifyDev_words (f : Device → Device) (hf : ∀ d, (f d).keypairs = d.keypairs) :
    SameView keyWords (modifyDev f) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  funext kid
  cases hd : w.dev <;> simp [keyWords,hd,hf]

theorem keyWords_keep {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => keyWords (project w)) a) (pid kid : Nat) :
    ⦃fun w => ⌜KeyCompatible pid kid (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜KeyCompatible pid kid (project w)⌝⦄ := by
  apply hoare_consequence
    (ha.wp (fun words => ∀ word, words kid = some word → Affiliation.Compatible word pid))
  · intro w h; exact compatible_words.mp h
  · intro x w h; exact compatible_words.mpr h

theorem setPeer_words (pid : PeerId) (p : Peer) : SameView keyWords (setPeer pid p) :=
  modifyDev_words _ (fun _ => rfl)

theorem peerGet_words (pid : PeerId) : SameView keyWords (peerGet pid) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  obtain ⟨d,p,hd,hp,pos,hk⟩ := peerGet_loan pid w v ambient ambient' hr
  have hdev := congrArg WGStoreView.dev hk
  change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} at hdev
  change w.dev = some d at hd
  unfold keyWords
  rw [hdev,hd]
  rfl

theorem peerPut_words (pid : Option PeerId) : SameView keyWords (peerPut pid) := by
  intro initial
  let P : WGWorld → Prop := fun w => keyWords w = initial
  have getter (id : PeerId) : Preserves P (getPeer id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' h hr
    obtain ⟨rfl,_,_,_,_⟩ := getPeer_normal id w v p ambient ambient' hr
    exact h
  have setter := fun id p => (setPeer_words id p).wp (fun words => words = initial)
  have erase := fun id (p : Peer) =>
    (modifyDev_words (fun d => {d with txDropped := d.txDropped + p.staged.length, peers := d.peers.erase id})
      (fun _ => rfl)).wp (fun words => words = initial)
  have indices (action : IndexM Unit) : Preserves P (liftIndex action) := by
    apply hoare_liftIndex
    intro w d table hi hd
    unfold P keyWords at *
    simpa only [hd,Option.bind_some] using hi
  change Preserves P (peerPut pid)
  unfold peerPut refcountDecAndTest requireNotPending
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported,liftM]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact getter _)
    | (index_material_head setPeer; exact setter _ _)
    | (index_material_head modifyDev; exact erase _ _)
    | (index_material_head retirePeerUnits; unfold retirePeerUnits)
    | (index_material_head modifyAmbient; unfold modifyAmbient)
    | (index_material_head modify
       apply hoare_modify
       intro w hi
       exact hi)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | credit_component indices
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

theorem queued_words (pid : PeerId) (retry : Bool) : SameView keyWords (sendQueuedHandshakeInitiation pid retry) := by
  intro initial
  let P : WGWorld → Prop := fun w => keyWords w = initial
  have getter (id : PeerId) : Preserves P (getPeer id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' h hr
    obtain ⟨rfl,_,_,_,_⟩ := getPeer_normal id w v p ambient ambient' hr
    exact h
  have setter := fun p => (setPeer_words pid p).wp (fun words => words = initial)
  have hg := (peerGet_words pid).wp (fun words => words = initial)
  have hp := (peerPut_words (some pid)).wp (fun words => words = initial)
  have ht := fun date => (branchExpired_sameWGWorld .queuedNotExpired date REKEY_TIMEOUT (!·)).wp P
  have hm := (modifyDev_words (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl)).wp (fun words => words = initial)
  change Preserves P (sendQueuedHandshakeInitiation pid retry)
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact getter _)
    | (index_material_head setPeer; exact setter _)
    | (index_material_head peerGet; exact hg)
    | (index_material_head peerPut; exact hp)
    | (index_material_head branchExpired; exact ht _)
    | (index_material_head modifyDev; exact hm)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

theorem keyUpdate_protect (id : KeypairId) (f : Keypair → Keypair) :
    SameView protectView (do let k ← getKeypair id; setKeypair id (f k)) := by
  have hg : SameView protectView (getKeypair id) := by
    apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient key v ambient' hr
    obtain ⟨rfl,_,_,_,_⟩ := KeyTimes.getKeypair_return id w v key ambient ambient' hr
    rfl
  apply SameView.bind hg
  intro k
  exact modifyDev_protect _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem keyUpdate_compatible (pid kid target : Nat) (f : Keypair → Keypair)
    (hf : ∀ k, Affiliation.keyCell (f k) = Affiliation.keyCell k) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ (do let k ← getKeypair target; setKeypair target (f k))
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  simp only [compatible_factor]
  apply hoare_bind _ _ (Affiliation.getKeypair_spec (compatibleState pid kid) target)
  intro k
  apply hoare_consequence (Affiliation.setKeypair_spec (compatibleState pid kid) target (f k))
  · intro w h
    exact ⟨h.1,by simpa only [hf] using h.2⟩
  · intro x w h; exact h

theorem transfer_getPeer (initial : WGWorld) (pid : PeerId) :
    ⦃fun w => ⌜Transfer initial w⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜Transfer initial w ∧ protectPeerAt w pid = some (protectCell p)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' h hr
  obtain ⟨rfl,_,d,hd,hp⟩ := getPeer_normal pid w v p ambient ambient' hr
  exact ⟨h,by simp [protectPeerAt,hd,hp]⟩

theorem transfer_setPeer (initial : WGWorld) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜Transfer initial w ∧ protectPeerAt w pid = some (protectCell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  have he := (hoare_iff_run_ambient _ _ _).mp
    (setPeer_protect_spec (fun t => t = protectView w) pid p) w ambient x v ambient' ⟨rfl,h.2⟩ hr
  exact h.1.after_view he

theorem setKeypair_protect (id : KeypairId) (k : Keypair) : SameView protectView (setKeypair id k) :=
  modifyDev_protect _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem stagedOutNokey_transfers (pid : PeerId) (packets : List WG.Packet) (kp : Option KeypairId) (invalid : Bool) :
    Transfers (Lifetimes.stagedOutNokey pid packets kp invalid) := by
  apply (Transfers.iff_run_ambient _).mpr
  intro w ambient x v ambient' hr
  let tail : WG.M Unit := do
    keypairPut kp false
    for _ in packets do _ ← branch .stagedOrphanWalk true
    _ ← branch .stagedOrphanWalk false
    let p ← getPeer pid
    setPeer pid {p with staged := packets ++ p.staged}
    sendQueuedHandshakeInitiation pid false
  have ht : Preserves (Transfer w) tail := by
    unfold tail
    apply preserves_bind (transfer_frame (project := id) (keypairPut_protect kp false) w)
    intro _
    apply preserves_bind
    · apply list_view_spec id (Transfer w)
      intro pkt acc
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .stagedOrphanWalk true) (Transfer w))
      intro _
      exact preserves_pure _
    · intro _
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .stagedOrphanWalk false) (Transfer w))
      intro _
      apply hoare_bind _ _ (transfer_getPeer w pid)
      intro p
      apply hoare_bind _ _ (hoare_consequence (transfer_setPeer w pid {p with staged := packets ++ p.staged})
        (fun _ h => ⟨h.1,by simpa only [protectCell] using h.2⟩) (fun _ _ h => h))
      intro _
      exact Transfers.wp (sendQueued_transfers pid false) w
  have spec : Preserves (Transfer w) (Lifetimes.stagedOutNokey pid packets kp invalid) := by
    unfold Lifetimes.stagedOutNokey
    simp only [getPeer_twice]
    cases invalid with
    | false => exact ht
    | true =>
      cases kp with
      | none =>
        apply preserves_bind (hoare_liftAmbient (AmbientM.invariant "unreachable") (Transfer w))
        intro _
        exact ht
      | some target =>
        apply preserves_bind
        · apply (hoare_iff_run_ambient _ _ _).mpr
          intro a aa k b ab h run
          obtain ⟨rfl,_,_,_,_⟩ := KeyTimes.getKeypair_return target a b k aa ab run
          exact h
        · intro k
          apply preserves_bind (transfer_frame (project := id)
            (setKeypair_protect target {k with sending := {k.sending with isValid := false}}) w)
          intro _
          exact ht
  exact (hoare_iff_run_ambient _ _ _).mp spec w ambient x v ambient' (Transfer.refl w) hr

theorem stagedOutNokey_compatible (pid kid : Nat) (packets : List WG.Packet) (kp : Option KeypairId) (invalid : Bool) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ Lifetimes.stagedOutNokey pid packets kp invalid
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  let tail : WG.M Unit := do
    keypairPut kp false
    for _ in packets do _ ← branch .stagedOrphanWalk true
    _ ← branch .stagedOrphanWalk false
    let p ← getPeer pid
    setPeer pid {p with staged := packets ++ p.staged}
    sendQueuedHandshakeInitiation pid false
  have ht : Preserves (KeyCompatible pid kid) tail := by
    unfold tail
    apply preserves_bind (keypairPut_compatible pid kid kp false)
    intro _
    apply preserves_bind
    · apply list_view_spec id (KeyCompatible pid kid)
      intro pkt acc
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .stagedOrphanWalk true) (KeyCompatible pid kid))
      intro _
      exact preserves_pure _
    · intro _
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .stagedOrphanWalk false) (KeyCompatible pid kid))
      intro _
      apply preserves_bind
      · apply (hoare_iff_run_ambient _ _ _).mpr
        intro w ambient p v ambient' h hr
        obtain ⟨rfl,_,_,_,_⟩ := getPeer_normal pid w v p ambient ambient' hr
        exact h
      · intro p
        apply preserves_bind (setPeer_compatible pid kid pid {p with staged := packets ++ p.staged})
        intro _
        exact keyWords_keep (project := id) (queued_words pid false) pid kid
  change Preserves (KeyCompatible pid kid) _
  unfold Lifetimes.stagedOutNokey
  simp only [getPeer_twice]
  cases invalid with
  | false => exact ht
  | true =>
    cases kp with
    | none =>
      apply preserves_bind (hoare_liftAmbient (AmbientM.invariant "unreachable") (KeyCompatible pid kid))
      intro _
      exact ht
    | some target =>
      have getter := Affiliation.getKeypair_spec (compatibleState pid kid) target
      simp only [← compatible_factor] at getter
      apply hoare_bind _ _ getter
      intro k
      have setter := Affiliation.setKeypair_spec (compatibleState pid kid) target
        {k with sending := {k.sending with isValid := false}}
      simp only [← compatible_factor] at setter
      apply hoare_bind _ _ (hoare_consequence setter
        (fun _ h => ⟨h.1,by simpa only [Affiliation.keyCell] using h.2⟩)
        (fun _ _ h => h))
      intro _
      exact ht

def StageInv (initial : WGWorld) (pid kid : Nat) (w : WGWorld) := Transfer initial w ∧ KeyCompatible pid kid w

theorem stage_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) (initial : WGWorld) (pid kid : Nat) :
    ⦃fun w => ⌜StageInv initial pid kid (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜StageInv initial pid kid (project w)⌝⦄ := by
  apply hoare_consequence
    (ha.wp (fun store => ∃ w, StageInv initial pid kid w ∧ store = wgStoreView w))
  · intro w h; exact ⟨project w,h,rfl⟩
  · intro x v h
    obtain ⟨w,h,he⟩ := h
    refine ⟨transfer_stable initial w (project v) he h.1,?_⟩
    have hd := congrArg WGStoreView.dev he
    change (project v).dev = w.dev at hd
    simpa only [KeyCompatible,hd] using h.2

theorem stage_getKey (initial : WGWorld) (pid kid target : Nat) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ getKeypair target
    ⦃⇓? k w => ⌜StageInv initial pid kid w ∧ Affiliation.keyAt w target = some (Affiliation.keyCell k)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient k v ambient' h hr
  obtain ⟨rfl,_,d,hd,hk⟩ := KeyTimes.getKeypair_return target w v k ambient ambient' hr
  exact ⟨h,by simp [Affiliation.keyAt,hd,hk]⟩

theorem stage_setKey (initial : WGWorld) (pid kid target : Nat) (k : Keypair) :
    ⦃fun w => ⌜StageInv initial pid kid w ∧ Affiliation.keyAt w target = some (Affiliation.keyCell k)⌝⦄ setKeypair target k
    ⦃⇓? _ w => ⌜StageInv initial pid kid w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  refine ⟨h.1.1.after_view
    ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp (setKeypair_protect target k)
      w ambient x v ambient' hr),?_⟩
  rw [compatible_factor]
  exact (hoare_iff_run_ambient _ _ _).mp (Affiliation.setKeypair_spec (compatibleState pid kid) target k)
    w ambient x v ambient' ⟨compatible_factor.mp h.1.2,h.2⟩ hr

theorem stage_outNokey (initial : WGWorld) (pid kid : Nat) (packets : List WG.Packet) (kp : Option KeypairId) (invalid : Bool) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ Lifetimes.stagedOutNokey pid packets kp invalid
    ⦃⇓? _ w => ⌜StageInv initial pid kid w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  exact ⟨h.1.trans ((Transfers.iff_run_ambient _).mp
    (stagedOutNokey_transfers pid packets kp invalid) w ambient x v ambient' hr),
    (hoare_iff_run_ambient _ _ _).mp (stagedOutNokey_compatible pid kid packets kp invalid)
      w ambient x v ambient' h.2 hr⟩

def stagedSubmit (pid kid : Nat) (packets : List DataPacket) : WG.M Unit := do
  Affiliation.sendAcquire kid
  let item ← packets.mapM newTxSkb
  createData pid item

theorem stage_submit (initial : WGWorld) (pid kid : Nat) (packets : List DataPacket) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ stagedSubmit pid kid packets
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  cases x
  exact h.1.trans (stagedSubmit_handoff packets h.2 ambient ambient' hr)

/-- Literal continuation after the optional current-key get. -/
def stagedKeySource (pid kid : Nat) (packets : List WG.Packet) : WG.M Unit := do
  let k ← getKeypair kid
  if ← branch .stagedKeyInvalid !k.sending.isValid then return ← Lifetimes.stagedOutNokey pid packets (some kid) false
  if ← branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME then
    return ← Lifetimes.stagedOutNokey pid packets (some kid) true
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← branch .stagedNonceIterate true
    let ds ← ipTunnelEcnEncap pkt
    let k ← getKeypair kid
    let nonce := k.sendingCounter
    setKeypair kid {k with sendingCounter := k.sendingCounter+1}
    if ← branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES then
      return ← Lifetimes.stagedOutNokey pid packets (some kid) true
    packetsCb := packetsCb ++ [{peer:=pid,keypair:=kid,nonce,plaintext:=pkt,ds}]
  _ ← branch .stagedNonceIterate false
  stagedSubmit pid kid packetsCb

theorem stagedKeySource_spec (initial : WGWorld) (pid kid : Nat) (packets : List WG.Packet) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ stagedKeySource pid kid packets
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  let P := StageInv initial pid kid
  let nonceStep : WG.M Nat := do
    let k ← getKeypair kid
    setKeypair kid {k with sendingCounter := k.sendingCounter + 1}
    pure k.sendingCounter
  have nonce_spec : Preserves P nonceStep := by
    unfold nonceStep
    apply hoare_bind _ _ (stage_getKey initial pid kid kid)
    intro k
    apply hoare_bind _ _ (hoare_consequence
      (stage_setKey initial pid kid kid {k with sendingCounter := k.sendingCounter + 1})
      (fun _ h => ⟨h.1,by simpa only [Affiliation.keyCell] using h.2⟩)
      (fun _ _ h => h))
    intro _
    exact preserves_pure _
  have getter := hoare_consequence (stage_getKey initial pid kid kid)
    (fun _ h => h) (fun _ _ h => h.1)
  have expired := fun date =>
    (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp P
  have ecn := fun pkt => (Lifetimes.ipTunnelEcnEncap_sameWGWorld pkt).wp P
  have out := stage_outNokey initial pid kid packets (some kid)
  have submit := stage_submit initial pid kid
  have weaken {α : Type} (a : WG.M α) (h : Preserves P a) :
      Hoare a P (fun _ w => Transfer initial w) :=
    hoare_consequence h (fun _ h => h) (fun _ _ h => h.1)
  have step {α β : Type} (a : WG.M α) (f : α → WG.M β)
      (Q : β → WGWorld → Prop) (ha : Preserves P a)
      (hf : ∀ x, Hoare (f x) P Q) : Hoare (a >>= f) P Q :=
    hoare_bind a f ha hf
  have source : stagedKeySource pid kid packets = (do
      let k ← getKeypair kid
      if ← branch .stagedKeyInvalid !k.sending.isValid then
        return ← Lifetimes.stagedOutNokey pid packets (some kid) false
      if ← branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME then
        return ← Lifetimes.stagedOutNokey pid packets (some kid) true
      let mut packetsCb : List DataPacket := []
      for pkt in packets do
        _ ← branch .stagedNonceIterate true
        let ds ← ipTunnelEcnEncap pkt
        let nonce ← nonceStep
        if ← branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES then
          return ← Lifetimes.stagedOutNokey pid packets (some kid) true
        packetsCb := packetsCb ++ [{peer := pid,keypair := kid,nonce,plaintext := pkt,ds}]
      _ ← branch .stagedNonceIterate false
      stagedSubmit pid kid packetsCb) := by
    simp only [stagedKeySource,nonceStep,bind_assoc,pure_bind]
  rw [source]
  change Hoare _ P (fun _ w => Transfer initial w)
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | unfold Preserves
    | exact nonce_spec
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter)
    | (index_material_head branchExpired; exact expired _)
    | (index_material_head ipTunnelEcnEncap; exact ecn _)
    | (index_material_head Lifetimes.stagedOutNokey; first | exact out _ | exact weaken _ (out _))
    | (index_material_head stagedSubmit; exact submit _)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | (index_material_head Pure.pure; first | exact preserves_pure _ | exact weaken _ (preserves_pure _))
    | (index_material_head Bind.bind; apply step)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

def SelectInv (initial : WGWorld) (pid : PeerId) (kp : Option KeypairId) (w : WGWorld) : Prop :=
  Transfer initial w ∧ ∀kid, kp = some kid → KeyCompatible pid kid w

def SelectPending (initial : WGWorld) (pid : PeerId) (p : Peer) (w : WGWorld) : Prop :=
  SelectInv initial pid p.keypairCurrent w ∧ protectPeerAt w pid = some (protectCell p)

theorem select_stable (initial : WGWorld) (pid : PeerId) (kp : Option KeypairId) : WGStoreStable (SelectInv initial pid kp) := by
  intro w v hk h
  have hd := congrArg WGStoreView.dev hk
  change v.dev = w.dev at hd
  exact ⟨transfer_stable initial w v hk h.1,by simpa only [KeyCompatible,hd] using h.2⟩
theorem selectPending_stable (initial : WGWorld) (pid : PeerId) (p : Peer) : WGStoreStable (SelectPending initial pid p) := by
  intro w v hk h
  have hd := congrArg WGStoreView.dev hk
  change v.dev = w.dev at hd
  exact ⟨select_stable initial pid p.keypairCurrent w v hk h.1,by simpa only [protectPeerAt,hd] using h.2⟩

theorem select_getPeer (initial : WGWorld) (pid : PeerId) :
    ⦃fun w => ⌜Transfer initial w ∧ CurrentCompatible pid w⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜SelectPending initial pid p w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' h hr
  obtain ⟨rfl,_,d,hd,hp⟩ := getPeer_normal pid w v p ambient ambient' hr
  exact ⟨⟨h.1,fun kid hk => h.2 d p kid hd hp hk⟩,by simp [protectPeerAt,hd,hp]⟩

theorem select_setPeer (initial : WGWorld) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜SelectPending initial pid p w⌝⦄ setPeer pid {p with staged:=[]}
    ⦃⇓? _ w => ⌜SelectInv initial pid p.keypairCurrent w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (transfer_setPeer initial pid {p with staged:=[]})
    w ambient x v ambient' ⟨h.1.1,h.2⟩ hr,?_⟩
  intro kid hk
  exact (hoare_iff_run_ambient _ _ _).mp (setPeer_compatible pid kid pid {p with staged:=[]})
    w ambient x v ambient' (h.1.2 kid hk) hr

theorem select_keyGet (initial : WGWorld) (pid : PeerId) (kp : Option KeypairId) :
    ⦃fun w => ⌜SelectInv initial pid kp w⌝⦄ keypairGet kp
    ⦃⇓? result w => ⌜SelectInv initial pid result w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' h hr
  have hf := (hoare_iff_run_ambient _ _ _).mp
    (Affiliation.keypairGet_affiliation kp (Affiliation.view w)) w ambient result v ambient' rfl hr
  refine ⟨h.1.after_view ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairGet_protect kp) w ambient result v ambient' hr),?_⟩
  intro kid hk
  have he : kp=some kid := by rcases hf.2 with hh|hh <;> simp_all
  rw [compatible_factor,hf.1]
  exact compatible_factor.mp (h.2 kid he)

def stagedFullSource (pid : PeerId) : WG.M Unit := do
  let p ← getPeer pid
  if ← branch .stagedEmpty p.staged.isEmpty then return
  setPeer pid {p with staged:=[]}
  let kp ← keypairGet p.keypairCurrent
  if ← branch .stagedNoKeypair kp.isNone then return ← Lifetimes.stagedOutNokey pid p.staged kp false
  let some kid := kp | invariant "unreachable"
  stagedKeySource pid kid p.staged

theorem bind_congr_source {m : Type → Type} [Monad m]
    (a : m α) (f g : α → m β) (h : ∀x,f x=g x) : a >>= f = a >>= g := by
  rw [funext h]

theorem stagedFullSource_eq (pid : PeerId) : stagedFullSource pid = sendStagedPackets pid := by
  rw [← Affiliation.sendStagedSource_eq]
  unfold stagedFullSource Affiliation.sendStagedSource
  apply bind_congr_source; intro p
  apply bind_congr_source; intro empty
  split
  · rfl
  · apply bind_congr_source; intro _
    apply bind_congr_source; intro kp
    apply bind_congr_source; intro absent
    split
    · rfl
    · cases kp <;> rfl

theorem staged_send_handoff (pid : PeerId) (hc : CurrentCompatible pid w)
    (ambient ambient' : Ambient)
    (hr : ((sendStagedPackets pid).run w).run ambient = .ok (((),v),ambient')) : Transfer w v := by
  rw [← stagedFullSource_eq] at hr
  simp only [stagedFullSource,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,a,aa,hget,empty,b,ab,hbranch,hr⟩ := hr
  have ha := (hoare_iff_run_ambient _ _ _).mp (select_getPeer w pid)
    w ambient p a aa ⟨Transfer.refl w,hc⟩ hget
  have hb := ((hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (SelectPending w pid p) .stagedEmpty p.staged.isEmpty)
    a aa empty b ab ha hbranch).2
  cases empty with
  | true =>
    simp only [ite_true] at hr
    cases hr
    exact hb.1.1
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨u,c,ac,hset,kp,d,ad,hkey,absent,e,ae,habsent,hr⟩ := hr
    have hc := (hoare_iff_run_ambient _ _ _).mp (select_setPeer w pid p)
      b ab u c ac hb hset
    have hd := (hoare_iff_run_ambient _ _ _).mp (select_keyGet w pid p.keypairCurrent)
      c ac kp d ad hc hkey
    have he := ((hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (SelectInv w pid kp) .stagedNoKeypair kp.isNone)
      d ad absent e ae hd habsent).2
    cases absent with
    | true =>
      simp only [ite_true] at hr
      exact (hoare_iff_run_ambient _ _ _).mp
        (Transfers.wp (stagedOutNokey_transfers pid p.staged kp false) w)
        e ae () v ambient' he.1 hr
    | false =>
      simp only [Bool.false_eq_true,ite_false] at hr
      cases kp with
      | none =>
        simp only [invariant,AmbientM.invariant] at hr
        cases hr
      | some kid =>
        exact (hoare_iff_run_ambient _ _ _).mp (stagedKeySource_spec w pid kid p.staged)
          e ae () v ambient' ⟨he.1,he.2 kid rfl⟩ hr

def currentKey (w : WGWorld) : PeerId → Option KeypairId :=
  fun pid => (w.dev.bind fun d => d.peers[pid]?).bind (·.keypairCurrent)
def controlView (w : WGWorld) := (protectView w,currentKey w,keyWords w)
def controlCell (p : Peer) := (protectCell p,p.keypairCurrent)
def controlAt (w : WGWorld) (pid : PeerId) := (w.dev.bind fun d => d.peers[pid]?).map controlCell

theorem control_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => controlView (project w)) a := by
  exact (protect_kernel ha).product
    ((ha.of_factor (fun store : WGStoreView => fun pid =>
      (store.dev.bind fun d => d.peers[pid]?).bind (·.keypairCurrent))
      (fun w => currentKey (project w)) (fun _ => rfl)).product (keyWords_kernel ha))

theorem control_getPeer (P : _ → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (controlView w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P (controlView w) ∧ controlAt w pid = some (controlCell p)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hi hr
  obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal pid w v p ambient ambient' hr
  exact ⟨hi,by simp [controlAt,hd,hp]⟩

theorem control_set_same (hd : w.dev = some d) (hp : d.peers[pid]? = some old)
    (hc : controlCell p = controlCell old) :
    controlView {w with dev := some {d with peers:=d.peers.insert pid p}} = controlView w := by
  have hs := protect_set_same (w:=w) hd hp (congrArg Prod.fst hc)
  have hk : p.keypairCurrent=old.keypairCurrent := congrArg Prod.snd hc
  apply Prod.ext hs
  apply Prod.ext
  · funext q
    by_cases hq : pid=q <;> simp_all [controlView,currentKey,Std.TreeMap.getElem?_insert]
  · funext kid; simp [controlView,keyWords,hd]

theorem control_setPeer (P : _ → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (controlView w) ∧ controlAt w pid = some (controlCell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜P (controlView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  cases hd : w.dev with
  | none => simp [controlAt,hd] at h
  | some d =>
    obtain ⟨old,hp,hc⟩ := Option.map_eq_some_iff.mp (by simpa [controlAt,hd] using h.2)
    cases hr
    simpa [setPeer,modifyDev,hd,control_set_same hd hp hc.symm] using h.1

theorem control_protect {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : SameView (fun w => controlView (project w)) a) :
    SameView (fun w => protectView (project w)) a := h.factor Prod.fst

theorem control_words {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : SameView (fun w => controlView (project w)) a) :
    SameView (fun w => keyWords (project w)) a := h.factor (fun t => t.2.2)

theorem current_factor : CurrentCompatible pid w ↔ ∀kid,currentKey w pid=some kid → KeyCompatible pid kid w := by
  constructor
  · intro h kid hk
    obtain ⟨p,hp,hkey⟩ := Option.bind_eq_some_iff.mp hk
    obtain ⟨d,hd,hslot⟩ := Option.bind_eq_some_iff.mp hp
    exact h d p kid hd hslot hkey
  · intro h d p kid hd hp hk
    exact h kid (by simp [currentKey,hd,hp,hk])

theorem control_current {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : SameView (fun w => controlView (project w)) a) (pid : PeerId) :
    ⦃fun w => ⌜CurrentCompatible pid (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜CurrentCompatible pid (project w)⌝⦄ := by
  simpa only [current_factor,compatible_words,controlView] using
    h.wp (fun obs => ∀ kid, obs.2.1 pid = some kid →
      ∀ word, obs.2.2 kid = some word → Affiliation.Compatible word pid)

theorem delTimer_control (pid : PeerId) (t : PeerTimer) : SameView controlView (delTimer pid t) := by
  intro s
  change Hoare (do let p ← getPeer pid; setPeer pid ((p.setTimer t none).setWheel t none))
    (fun w => controlView w = s) (fun _ w => controlView w = s)
  apply hoare_bind _ _ (control_getPeer (fun v => v=s) pid)
  intro p
  apply hoare_consequence (control_setPeer (fun v => v=s) pid _)
  · intro w h
    cases t <;> simpa only [controlCell,protectCell,Peer.setTimer,Peer.setWheel] using h
  · exact fun _ _ h => h

private theorem controlAt_view (he : controlView v = controlView w) (pid : PeerId) :
    controlAt v pid = controlAt w pid := by
  have hp := protectPeerAt_view (congrArg Prod.fst he) pid
  have hk := congrFun (congrArg (fun t => t.2.1) he) pid
  simp only [controlAt,controlView,currentKey,protectPeerAt] at *
  cases hv : (v.dev.bind fun d => d.peers[pid]?) <;>
    cases hw : (w.dev.bind fun d => d.peers[pid]?) <;>
      simp_all [controlCell]

private theorem control_getPeer_bind (initial : WGWorld) (pid : PeerId)
    (f : Peer → WG.M α)
    (hf : ∀ p, controlAt initial pid = some (controlCell p) →
      Preserves (fun w => controlView w = controlView initial) (f p)) :
    Preserves (fun w => controlView w = controlView initial) (getPeer pid >>= f) := by
  apply hoare_bind _ _ (control_getPeer (fun obs => obs = controlView initial) pid)
  intro p
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  have hp : controlAt initial pid = some (controlCell p) :=
    (controlAt_view h.1 pid).symm.trans h.2
  exact (hoare_iff_run_ambient _ _ _).mp (hf p hp) w ambient x v ambient' h.1 hr

private theorem control_setPeer_known (initial : WGWorld) (pid : PeerId) (p : Peer)
    (hp : controlAt initial pid = some (controlCell p)) :
    Preserves (fun w => controlView w = controlView initial) (setPeer pid p) := by
  apply hoare_consequence (control_setPeer (fun obs => obs = controlView initial) pid p)
  · intro w h
    exact ⟨h,(controlAt_view h pid).trans hp⟩
  · exact fun _ _ h => h

elab "rx_control_get_bind" : tactic => do
  let t := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  let args := t.getAppArgs
  unless (t.isAppOf ``Hoare || t.isAppOf ``Triple) && args.size ≥ 3 do
    Lean.throwError "not an endpoint contract"
  let a := args[args.size-3]!.consumeMData
  unless a.isAppOf ``Bind.bind && a.getAppArgs.size ≥ 2 do Lean.throwError "not a bind"
  let first := a.getAppArgs[a.getAppArgs.size-2]!.consumeMData
  unless first.isAppOf ``getPeer do Lean.throwError "not a peer read"

macro "rx_control_basic " initial:term : tactic => `(tactic|
  first
    | unfold Preserves
    | (rx_control_get_bind; apply control_getPeer_bind $initial; intro p hp)
    | (index_material_head setPeer; apply control_setPeer_known $initial)
    | (index_material_head getPeer
       exact hoare_consequence (control_getPeer (fun obs => obs = controlView $initial) _)
         (fun _ h => h) (fun _ _ h => h.1))
    | (index_material_head getDev; exact (control_kernel (project := id) Lifetimes.getDev_sameWGStore).wp (fun obs => obs = controlView $initial))
    | (first | index_material_head get | index_material_head MonadStateOf.get
       exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
    | (index_material_head modify; apply hoare_modify; intro w h; exact h)
    | material_join
    | material_join_use
    | (index_material_head Functor.discard; apply discard_view_spec controlView (fun obs => obs = controlView $initial))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | (first | index_material_head throw | index_material_head MonadExceptOf.throw
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' h hr
       cases hr)
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction)

theorem armTimer_control (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64) : SameView controlView (armTimer pid t delay jc) := by
  have timerCell (p : Peer) (timer : PeerTimer) (e : Option UInt64) :
      controlCell (p.setTimer timer e) = controlCell p := by cases timer <;> rfl
  have wheelCell (p : Peer) (timer : PeerTimer) (e : Option WheelEntry) :
      controlCell (p.setWheel timer e) = controlCell p := by cases timer <;> rfl
  have wheel (timer : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
      SameView controlView (placeOnWheel pid timer expires clk unit) := by
    apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro initial ambient x final ambient' hr
    have spec : Preserves (fun w => controlView w = controlView initial)
        (placeOnWheel pid timer expires clk unit) := by
      unfold placeOnWheel peekHiddenSite
      material_lower
      repeat' rx_control_basic initial
      all_goals try simp only [timerCell,wheelCell]
      all_goals assumption
    exact (hoare_iff_run_ambient _ _ _).mp spec initial ambient x final ambient' rfl hr
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro initial ambient x final ambient' hr
  have spec : Preserves (fun w => controlView w = controlView initial) (armTimer pid t delay jc) := by
    unfold armTimer
    material_lower
    repeat' first
      | (index_material_head placeOnWheel; exact (wheel _ _ _ _).wp (fun obs => obs = controlView initial))
      | rx_control_basic initial
  exact (hoare_iff_run_ambient _ _ _).mp spec initial ambient x final ambient' rfl hr

theorem modPeerTimer_control (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    SameView controlView (modPeerTimer site pid t delay) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro initial ambient x final ambient' hr
  have spec : Preserves (fun w => controlView w = controlView initial) (modPeerTimer site pid t delay) := by
    unfold modPeerTimer modPeerTimerGuard WG.andM
    material_lower
    repeat' first
      | (index_material_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w => controlView w = controlView initial))
      | (index_material_head armTimer; exact (armTimer_control _ _ _ _).wp (fun obs => obs = controlView initial))
      | rx_control_basic initial
  exact (hoare_iff_run_ambient _ _ _).mp spec initial ambient x final ambient' rfl hr

theorem timersHandshakeComplete_control (pid : PeerId) (site : HiddenSite) :
    SameView controlView (timersHandshakeComplete pid site) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro initial ambient x final ambient' hr
  have spec : Preserves (fun w => controlView w = controlView initial) (timersHandshakeComplete pid site) := by
    unfold timersHandshakeComplete
    material_lower
    repeat' first
      | (index_material_head delTimer; exact (delTimer_control _ _).wp (fun obs => obs = controlView initial))
      | rx_control_basic initial
    all_goals try simp only [controlCell,protectCell]
    all_goals assumption
  exact (hoare_iff_run_ambient _ _ _).mp spec initial ambient x final ambient' rfl hr

theorem timersDataReceived_control (pid : PeerId) : SameView controlView (timersDataReceived pid) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro initial ambient x final ambient' hr
  have spec : Preserves (fun w => controlView w = controlView initial) (timersDataReceived pid) := by
    unfold timersDataReceived
    material_lower
    repeat' first
      | (index_material_head modPeerTimer; exact (modPeerTimer_control _ _ _ _).wp (fun obs => obs = controlView initial))
      | rx_control_basic initial
    all_goals try simp only [controlCell,protectCell]
    all_goals assumption
  exact (hoare_iff_run_ambient _ _ _).mp spec initial ambient x final ambient' rfl hr

theorem timersTraversal_control (pid : PeerId) : SameView controlView (timersTraversal pid) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro initial ambient x final ambient' hr
  have spec : Preserves (fun w => controlView w = controlView initial) (timersTraversal pid) := by
    unfold timersTraversal
    material_lower
    repeat' first
      | (index_material_head modPeerTimer; exact (modPeerTimer_control _ _ _ _).wp (fun obs => obs = controlView initial))
      | rx_control_basic initial
    all_goals try simp only [controlCell,protectCell]
    all_goals assumption
  exact (hoare_iff_run_ambient _ _ _).mp spec initial ambient x final ambient' rfl hr

theorem dstCacheReset_control (pid : PeerId) : SameView controlView (dstCacheReset pid) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro initial ambient x final ambient' hr
  have spec : Preserves (fun w => controlView w = controlView initial) (dstCacheReset pid) := by
    unfold dstCacheReset
    material_lower
    repeat' first
      | rx_control_basic initial
    all_goals try simp only [controlCell,protectCell]
    all_goals assumption
  exact (hoare_iff_run_ambient _ _ _).mp spec initial ambient x final ambient' rfl hr

theorem setPeerEndpoint_control (pid : PeerId) (e : Endpoint) : SameView controlView (setPeerEndpoint pid e) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro initial ambient x final ambient' hr
  have spec : Preserves (fun w => controlView w = controlView initial) (setPeerEndpoint pid e) := by
    unfold setPeerEndpoint requireNotPending
    material_lower
    repeat' first
      | (index_material_head endpointEq; exact (control_kernel (project := id) (Lifetimes.endpointEq_sameStore _ _)).wp (fun obs => obs = controlView initial))
      | (index_material_head dstCacheReset; exact (dstCacheReset_control _).wp (fun obs => obs = controlView initial))
      | rx_control_basic initial
    all_goals try simp only [controlCell,protectCell]
    all_goals assumption
  exact (hoare_iff_run_ambient _ _ _).mp spec initial ambient x final ambient' rfl hr

theorem updateRxStats_protect (pid : PeerId) (len : Nat) : SameView protectView (updateRxStats pid len) := by
  have hm := modifyDev_protect (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hp := modifyPeer_protect pid (fun p => {p with rxBytes := p.rxBytes + len}) (fun _ => rfl)
  exact SameView.bind hm (fun _ => hp)

theorem dishonest_protect (why : Dishonest) : SameView protectView (dishonest why) :=
  modifyDev_protect _ (fun _ => by cases why <;> rfl) (fun _ => by cases why <;> rfl)
    (fun _ => by cases why <;> rfl) (fun _ => by cases why <;> rfl)

elab "rx_credit_mark_head" : tactic => do
  let t := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  let args := t.getAppArgs
  unless (t.isAppOf ``Hoare || t.isAppOf ``Triple) && args.size ≥ 3 do
    Lean.throwError "not an endpoint contract"
  let a := args[args.size-3]!.consumeMData
  unless a.isAppOf ``Bind.bind && a.getAppArgs.size ≥ 2 do Lean.throwError "not a bind"
  let aa := a.getAppArgs
  unless aa[aa.size-2]!.consumeMData.isAppOf ``getPeer do Lean.throwError "not a peer read"
  let .lam _ _ body _ := aa.back!.consumeMData | Lean.throwError "not a continuation"
  let body := body.consumeMData
  unless body.isAppOf ``Bind.bind && body.getAppArgs.size ≥ 2 do Lean.throwError "not a chained update"
  let ba := body.getAppArgs
  unless ba[ba.size-2]!.consumeMData.isAppOf ``setPeer do Lean.throwError "not a peer update"

theorem keepKeyFreshRx_transfers (pid : PeerId) : Transfers (keepKeyFreshRx pid) := by
  apply (Transfers.iff_run_ambient _).mpr
  intro initial ambient x final ambient' hr
  let P := Transfer initial
  have getter (target : PeerId) : Preserves P (getPeer target) :=
    hoare_consequence (transfer_getPeer initial target) (fun _ h => h) (fun _ _ h => h.1)
  have keyGetter (id : KeypairId) : Preserves P (getKeypair id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a key v b hi hk
    obtain ⟨rfl,_,_,_,_⟩ := KeyTimes.getKeypair_return id w v key a b hk
    exact hi
  have mark : Preserves P (do
      let p ← getPeer pid
      setPeer pid {p with sentLastminuteHandshake := true}) :=
    transfer_frame (project := id)
      (modifyPeer_protect pid (fun p => {p with sentLastminuteHandshake := true}) (fun _ => rfl)) initial
  have tail : Preserves P (do
      let p ← getPeer pid
      setPeer pid {p with sentLastminuteHandshake := true}
      sendQueuedHandshakeInitiation pid false) := by
    have composed := hoare_bind
      (do let p ← getPeer pid; setPeer pid {p with sentLastminuteHandshake := true})
      (fun _ => sendQueuedHandshakeInitiation pid false) mark
      (fun _ => Transfers.wp (project := id) (sendQueued_transfers pid false) initial)
    simpa only [bind_assoc,Preserves,P,id_eq] using composed
  have spec : Preserves P (keepKeyFreshRx pid) := by
    unfold keepKeyFreshRx WG.andM
    material_lower
    repeat' first
      | unfold Preserves
      | (rx_credit_mark_head; exact tail)
      | (index_material_head getPeer; exact getter _)
      | (index_material_head getKeypair; exact keyGetter _)
      | (index_material_head branchExpired; exact (branchExpired_sameWGWorld _ _ _).wp P)
      | (index_material_head Pure.pure; exact preserves_pure _)
      | (index_material_head Bind.bind; apply preserves_bind)
      | material_component
      | material_join
      | material_join_use
      | material_intro
      | (index_material_head ite; split)
      | material_reduce
      | material_match
      | contradiction
  exact (hoare_iff_run_ambient _ _ _).mp spec initial ambient x final ambient' (Transfer.refl initial) hr

theorem stage_control {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => controlView (project w)) a) (initial : WGWorld) (pid kid : Nat) :
    ⦃fun w => ⌜StageInv initial pid kid (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜StageInv initial pid kid (project w)⌝⦄ := by
  apply hoare_consequence
    (ha.wp (fun obs => ∃ w, StageInv initial pid kid w ∧ obs = controlView w))
  · intro w h; exact ⟨project w,h,rfl⟩
  · intro x v h
    obtain ⟨w,h,he⟩ := h
    refine ⟨h.1.after_view (congrArg Prod.fst he),?_⟩
    have hk : keyWords (project v) = keyWords w := congrArg (fun obs => obs.2.2) he
    rw [compatible_words]
    simpa only [hk] using compatible_words.mp h.2

def AfterPromotion (initial : WGWorld) (pid : PeerId) (newKey : Bool) (w : WGWorld) :=
  Transfer initial w ∧ (newKey=true → CurrentCompatible pid w)

theorem afterPromotion_stable (initial : WGWorld) (pid : PeerId) (newKey : Bool) :
    WGStoreStable (AfterPromotion initial pid newKey) := by
  intro w v hk h
  have hd := congrArg WGStoreView.dev hk
  change v.dev = w.dev at hd
  exact ⟨transfer_stable initial w v hk h.1,
    by simpa only [CurrentCompatible,KeyCompatible,hd] using h.2⟩

theorem receivedWithKeypair_prepare (initial : WGWorld) (pid kid : Nat) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ receivedWithKeypair pid kid
    ⦃⇓? result w => ⌜AfterPromotion initial pid result w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' h hr
  refine ⟨h.1.after_view ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (receivedWithKeypair_protect pid kid) w ambient result v ambient' hr),?_⟩
  intro he; subst result
  exact receivedWithKeypair_current_compatible h.2 ambient ambient' hr

theorem current_control {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => controlView (project w)) a) (initial : WGWorld) (pid : PeerId) :
    ⦃fun w => ⌜Transfer initial (project w) ∧ CurrentCompatible pid (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜Transfer initial (project w) ∧ CurrentCompatible pid (project w)⌝⦄ := by
  apply hoare_consequence
    (ha.wp (fun obs => ∃ w, (Transfer initial w ∧ CurrentCompatible pid w) ∧ obs = controlView w))
  · intro w h; exact ⟨project w,h,rfl⟩
  · intro x v h
    obtain ⟨w,h,he⟩ := h
    refine ⟨h.1.after_view (congrArg Prod.fst he),?_⟩
    have hc : currentKey (project v) = currentKey w := congrArg (fun obs => obs.2.1) he
    have hk : keyWords (project v) = keyWords w := congrArg (fun obs => obs.2.2) he
    rw [current_factor]
    intro kid hkid
    have hold := current_factor.mp h.2 kid (hc ▸ hkid)
    rw [compatible_words]
    simpa only [hk] using compatible_words.mp hold

theorem staged_send_spec (initial : WGWorld) (pid : PeerId) :
    ⦃fun w => ⌜Transfer initial w ∧ CurrentCompatible pid w⌝⦄ sendStagedPackets pid
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  cases x
  exact h.1.trans (staged_send_handoff pid h.2 ambient ambient' hr)

def promoteAndSend (pid kid : Nat) : WG.M Unit := do
  if ← branch .doneReceivedNew (← receivedWithKeypair pid kid) then
    timersHandshakeComplete pid .walltimeLastHandshakeData
    sendStagedPackets pid

theorem promoteAndSend_transfer (initial : WGWorld) (pid kid : Nat) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ promoteAndSend pid kid
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  unfold promoteAndSend
  apply hoare_bind _ _ (receivedWithKeypair_prepare initial pid kid)
  intro newKey
  apply hoare_bind _ _ (branch_predicate_native (AfterPromotion initial pid newKey) .doneReceivedNew newKey)
  intro result
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  obtain ⟨he,h⟩ := h
  subst result
  cases newKey with
  | false =>
    cases hr
    exact h.1
  | true =>
    have hh := current_control (project := id)
      (timersHandshakeComplete_control pid .walltimeLastHandshakeData) initial pid
    have hs := staged_send_spec initial pid
    have composed := hoare_bind _ _ hh (fun _ => hs)
    exact (hoare_iff_run_ambient _ _ _).mp composed w ambient x v ambient'
      ⟨h.1,h.2 rfl⟩ hr

def prepareRest (pid : PeerId) (pkt : RxPacket) : WG.M (Option Packets.RxReady) := do
  keepKeyFreshRx pid
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  let bytes := pkt.bytes
  let len := bytes.length   -- skb->len
  let reject (why : Dishonest) : WG.M (Option Packets.RxReady) := do
    dishonest why   -- then packet_processed: dev_kfree_skb
    return none
  -- a packet with length 0 is a keepalive
  if ← branch .doneRxKeepalive (len == 0) then
    updateRxStats pid MESSAGE_DATA_LEN_0   -- message_data_len(0)
    return none
  timersDataReceived pid
  -- `skb_network_header(skb) < skb->head`: the decrypted skb's network header is its data
  if ← branch .doneNetworkBelowHead false then return ← reject .size
  -- `!(pskb_network_may_pull(skb, sizeof(struct iphdr)) && (version == 4 ||
  -- (version == 6 && pskb_network_may_pull(skb, sizeof(struct ipv6hdr)))))`
  let version := (bytes.headD 0).toNat / 16
  let honest ← WG.andM (branch .doneMayPullV4 (len ≥ 20)) do
    WG.orM (branch .doneVersion4 (version == 4)) do
      WG.andM (branch .doneVersion6 (version == 6)) (branch .doneMayPullV6 (len ≥ 40))
  if !honest then return ← reject .type
  -- skb->ip_summed = CHECKSUM_UNNECESSARY; csum_level = ~0
  let protocol := ipTunnelParseProtocol bytes
  let ds := pkt.ds   -- PACKET_CB(skb)->ds
  let mut ipLen := 0
  let mut bytes := bytes
  if ← branch .doneProtoIp (protocol == 4) then
    ipLen := beAt bytes 2 2   -- ntohs(ip_hdr(skb)->tot_len)
    if ← branch .doneV4TooShort (ipLen < 20) then return ← reject .size
    bytes ← inetEcnDecapsulate 4 ds bytes   -- INET_ECN_decapsulate(skb, ds, ip_hdr(skb)->tos)
  else if ← branch .doneProtoIpv6 (protocol == 6) then
    ipLen := beAt bytes 4 2 + 40   -- ntohs(payload_len) + sizeof(struct ipv6hdr)
    bytes ← inetEcnDecapsulate 6 ds bytes   -- ..., ipv6_get_dsfield(ipv6_hdr(skb))
  else return ← reject .type
  if ← branch .doneLenBeyond (ipLen > len) then return ← reject .size
  let lenBeforeTrim := len
  -- pskb_trim(skb, len) of a linear skb
  if ← branch .doneTrimFailed false then return none
  return some ⟨protocol, bytes, ipLen, lenBeforeTrim⟩

theorem rxPrepare_factor (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Packets.rxPrepare pid pkt endpoint = (do
      setPeerEndpoint pid endpoint
      promoteAndSend pid pkt.keypair
      prepareRest pid pkt) := by
  simp only [Packets.rxPrepare,promoteAndSend,prepareRest,bind_assoc,bind_if_source,pure_bind]

theorem prepareRest_transfer (initial : WGWorld) (pid : PeerId) (pkt : RxPacket) :
    ⦃fun w => ⌜Transfer initial w⌝⦄ prepareRest pid pkt
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  let P := Transfer initial
  change Preserves P (prepareRest pid pkt)
  unfold prepareRest timersAnyAuthenticatedPacketReceived WG.andM WG.orM
  material_lower
  repeat' first
    | unfold Preserves
    | (index_material_head keepKeyFreshRx; exact Transfers.wp (project := id) (keepKeyFreshRx_transfers _) initial)
    | (index_material_head delTimer; exact transfer_frame (project := id) (control_protect (project := id) (delTimer_control _ _)) initial)
    | (index_material_head timersTraversal; exact transfer_frame (project := id) (control_protect (project := id) (timersTraversal_control _)) initial)
    | (index_material_head timersDataReceived; exact transfer_frame (project := id) (control_protect (project := id) (timersDataReceived_control _)) initial)
    | (index_material_head updateRxStats; exact transfer_frame (project := id) (updateRxStats_protect _ _) initial)
    | (index_material_head dishonest; exact transfer_frame (project := id) (dishonest_protect _) initial)
    | (index_material_head inetEcnDecapsulate; exact transfer_frame (project := id)
        (protect_kernel (project := id) (Lifetimes.inetEcnDecapsulate_sameWGStore _ _ _)) initial)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_join
    | material_join_use
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

theorem rxPrepare_transfer (initial : WGWorld) (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    ⦃fun w => ⌜StageInv initial pid pkt.keypair w⌝⦄ Packets.rxPrepare pid pkt endpoint
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  rw [rxPrepare_factor]
  exact hoare_bind _ _ (stage_control (project := id) (setPeerEndpoint_control pid endpoint) initial pid pkt.keypair)
    (fun _ => hoare_bind _ _ (promoteAndSend_transfer initial pid pkt.keypair)
      (fun _ => prepareRest_transfer initial pid pkt))

def protectionOfBorrow (s : WGStoreView × (PeerId → Option Peer)) :=
  ((s.1.dev.map (·.ifindex),fun pid => (s.2 pid).map fun p => (p.internalId,p.refcount,p.rxQueue)),
   (s.1.dev.map (·.ifindex),fun (id : SkbId) => s.1.dev.bind fun d => d.rxSkbs[id]?),
   (fun pid => (s.2 pid).map fun p => p.txQueue.all),s.1.dev.map (·.sendWorkQueue))

theorem protection_borrow_factor (w : WGWorld) : protectView w = protectionOfBorrow (PeerBorrow.view w) := by
  unfold protectView protectionOfBorrow PeerBorrow.view PeerBorrow.outsidePeers PeerBorrow.resident
    peerView rxView handoffTxView sendView
  cases hd : w.dev <;> simp [wgStoreView,hd]

theorem lookupRepay_protect (protocol : Nat) (bytes : List UInt8) :
    SameView protectView (RxBorrow.source protocol bytes) :=
  (RxBorrow.source_frame protocol bytes).of_factor protectionOfBorrow protectView protection_borrow_factor

def rxFinishSource (pid : PeerId) (ready : Packets.RxReady) : WG.M (Option (List UInt8)) := do
  let routed ← RxBorrow.source ready.protocol ready.bytes
  if ← branch .doneDishonestPeer (routed != some pid) then
    dishonest .peer
    return none
  updateRxStats pid (ready.originalLen + MESSAGE_DATA_LEN_0)
  return some (ready.bytes.take ready.ipLen)

theorem rxFinishSource_eq (pid : PeerId) (ready : Packets.RxReady) : rxFinishSource pid ready = Packets.rxFinish pid ready := by
  simp only [rxFinishSource,Packets.rxFinish,Packets.rxAfterLookup,RxBorrow.source,RxBorrow.repayLookup,monadLift_self,bind_assoc,pure_bind]

theorem rxFinish_protect (pid : PeerId) (ready : Packets.RxReady) : SameView protectView (Packets.rxFinish pid ready) := by
  rw [← rxFinishSource_eq]
  intro s
  let P : WGWorld → Prop := fun w => protectView w = s
  change Preserves P (rxFinishSource pid ready)
  unfold rxFinishSource
  material_lower
  repeat' first
    | unfold Preserves
    | (index_material_head RxBorrow.source; exact (lookupRepay_protect _ _).wp (fun obs => obs = s))
    | (index_material_head dishonest; exact (dishonest_protect _).wp (fun obs => obs = s))
    | (index_material_head updateRxStats; exact (updateRxStats_protect _ _).wp (fun obs => obs = s))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

/-- Full original callback on its normal endpoints. The only owner hypothesis
is the packet key's nullable word compatibility at entry. -/
theorem consumeDataDone_handoff (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (hc : KeyCompatible pid pkt.keypair w) (ambient ambient' : Ambient)
    (hr : ((consumeDataDone pid pkt endpoint).run w).run ambient = .ok ((result,v),ambient')) :
    Transfer w v := by
  have spec : ⦃fun u => ⌜StageInv w pid pkt.keypair u⌝⦄ consumeDataDone pid pkt endpoint
      ⦃⇓? _ u => ⌜Transfer w u⌝⦄ := by
    rw [Packets.consumeDataDone_factor]
    apply hoare_bind _ _ (rxPrepare_transfer w pid pkt endpoint)
    intro ready
    cases ready with
    | none => exact preserves_pure none
    | some ready => exact transfer_frame (project := id) (rxFinish_protect pid ready) w
  exact (hoare_iff_run_ambient _ _ _).mp spec w ambient result v ambient' ⟨Transfer.refl w,hc⟩ hr

end Leanux.Proofs.WG.Queues.RxCredits
