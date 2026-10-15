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
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  cases hr
  intro d k hd hk
  cases hw : w.k.wg with
  | none => simp [setPeer,modifyDev,modifyK,hw] at hd
  | some old =>
    simp [setPeer,modifyDev,modifyK,hw] at hd
    subst d
    exact h old k hw hk

theorem modifyPeer_compatible (pid kid target : Nat) (f : Peer → Peer) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) target f)
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  change ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ (do let p ← getPeer target; setPeer target (f p))
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄
  have hs := fun p => setPeer_compatible pid kid target (f p)
  mvcgen [hs,getPeer,getDev,getK,invariant]

theorem receivedWithKeypair_compatible (pid kid : Nat) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ receivedWithKeypair pid kid
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  have hk := fun old => keypairPut_compatible pid kid old true
  have hm := modifyPeer_compatible pid kid pid
  mvcgen [receivedWithKeypair,hk,hm,getPeer,getDev,getK,branch,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [KeyCompatible]

theorem receivedWithKeypair_protect (pid kid : Nat) : SameView protectView (receivedWithKeypair pid kid) := by
  apply SameView.of_wp
  intro s
  have hk := fun old => (keypairPut_protect old true).wp (fun t => t=s)
  have hm := fun f hf => (modifyPeer_protect pid f hf).wp (fun t => t=s)
  mvcgen [receivedWithKeypair,hk,hm,getPeer,getDev,getK,branch,invariant]
  all_goals simp_all [protectCell]

def CurrentIs (pid kid : Nat) (w : World) : Prop :=
  ∀ d p, w.k.wg = some d → d.peers[pid]? = some p → p.keypairCurrent = some kid

theorem any_normal (a : M α) : ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  exact fun _ _ _ _ _ => True.intro

theorem install_current (pid kid : Nat) :
    ⦃fun _ => ⌜True⌝⦄ ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
      (fun p => {p with keypairCurrent := some kid, keypairNext := none}))
    ⦃⇓? _ w => ⌜CurrentIs pid kid w⌝⦄ := by
  change ⦃fun _ => ⌜True⌝⦄ (do let p ← getPeer pid; setPeer pid {p with keypairCurrent := some kid,keypairNext := none})
    ⦃⇓? _ w => ⌜CurrentIs pid kid w⌝⦄
  mvcgen [getPeer,getDev,getK,setPeer,modifyDev,modifyK,invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [CurrentIs]
  all_goals intro d p hd hp
  all_goals subst d
  all_goals simp at hp
  all_goals subst p
  all_goals rfl

theorem receivedWithKeypair_current (pid kid : Nat) :
    ⦃fun _ => ⌜True⌝⦄ receivedWithKeypair pid kid
    ⦃⇓? result w => ⌜result = true → CurrentIs pid kid w⌝⦄ := by
  have hm := any_normal ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
    (fun p => {p with keypairPrevious := p.keypairCurrent}))
  have hk := fun old => any_normal (keypairPut old true)
  have hs := install_current pid kid
  mvcgen [receivedWithKeypair,hm,hk,hs,getPeer,getDev,getK,branch,invariant]
  all_goals simp_all

/-- Promotion of this packet's key derives the staged-send precondition.
Erasure of an aliased old key is permitted; no receiving-validity premise. -/
theorem receivedWithKeypair_current_compatible (hc : KeyCompatible pid kid w)
    (hr : (receivedWithKeypair pid kid).run w = .ok (true,v)) : CurrentCompatible pid v := by
  have same := (hoare_iff_triple _ _ _).mpr (receivedWithKeypair_compatible pid kid) w true v hc hr
  have current := (hoare_iff_triple _ _ _).mpr (receivedWithKeypair_current pid kid) w true v True.intro hr rfl
  intro d p selected hd hp hs
  have eq := (current d p hd hp).symm.trans hs
  have he : kid=selected := Option.some.inj eq
  subst selected
  exact same

def keyWords (w : World) : KeypairId → Option (Option PeerId) :=
  fun kid => (w.k.wg.bind fun d => d.keypairs[kid]?).map (·.peer)

theorem compatible_words : KeyCompatible pid kid w ↔
    ∀ word, keyWords w kid = some word → Affiliation.Compatible word pid := by
  constructor
  · intro h word hw
    obtain ⟨k,hk,rfl⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨d,hd,hslot⟩ := Option.bind_eq_some_iff.mp hk
    exact h d k hd hslot
  · intro h d k hd hk
    exact h k.peer (by simp [keyWords,hd,hk])

theorem keyWords_kernel (ha : SameKernel a) : SameView keyWords a := by
  intro w x v hr
  unfold keyWords; rw [ha w x v hr]

theorem modifyDev_words (f : Device → Device) (hf : ∀d,(f d).keypairs=d.keypairs) :
    SameView keyWords (modifyDev f) := by
  intro w x v hr; cases hr
  funext kid; cases hd : w.k.wg <;> simp [keyWords,modifyDev,modifyK,hd,hf]

theorem keyWords_keep (ha : SameView keyWords a) (pid kid : Nat) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ a ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  rw [compatible_words] at h ⊢
  simpa only [ha w x v hr] using h

theorem setPeer_words (pid : PeerId) (p : Peer) : SameView keyWords (setPeer pid p) :=
  modifyDev_words _ (fun _ => rfl)

theorem peerGet_words (pid : PeerId) : SameView keyWords (peerGet pid) := by
  intro w x v hr
  obtain ⟨d,p,hd,hp,pos,hk⟩ := (hoare_iff_triple _ _ _).mpr (PeerBorrow.strict_acquire_spec pid w.k) w x v rfl hr
  unfold keyWords
  rw [hk]
  simp [hd]

theorem peerPut_words (pid : Option PeerId) : SameView keyWords (peerPut pid) := by
  apply SameView.of_wp
  intro s
  have hs := fun id p => (setPeer_words id p).wp (fun t => t=s)
  have hi := fun owner => (SameView.of_factor (indexRemove_sameIndexKernel owner)
    (fun (v : Kernel) => fun kid => (v.wg.bind fun d => d.keypairs[kid]?).map (fun (k : Keypair) => k.peer))
    keyWords (by intro w; funext kid; cases hd : w.k.wg <;> simp [keyWords,indexKernelView,indexKernel,hd])).wp (fun t => t=s)
  have hm := fun id (p : Peer) => (modifyDev_words (fun d => {d with txDropped := d.txDropped+p.staged.length,peers:=d.peers.erase id}) (fun _ => rfl)).wp (fun t => t=s)
  have hc := fun count => (keyWords_kernel (refcountDecAndTest_sameKernel count)).wp (fun t => t=s)
  mvcgen [peerPut,hs,hi,hm,hc,requireNotPending,getPeer,getDev,getK,branch,retirePeerUnits,invariant]
  all_goals try simp_all [keyWords]

theorem queued_words (pid : PeerId) (retry : Bool) : SameView keyWords (sendQueuedHandshakeInitiation pid retry) := by
  apply SameView.of_wp
  intro s
  have hs := fun p => (setPeer_words pid p).wp (fun t => t=s)
  have hg := (peerGet_words pid).wp (fun t => t=s)
  have hp := (peerPut_words (some pid)).wp (fun t => t=s)
  have ht := fun date => (keyWords_kernel (branchExpired_sameKernel .queuedNotExpired date REKEY_TIMEOUT (!·))).wp (fun t => t=s)
  have hr := (keyWords_kernel (Lifetimes.recordQueued_sameKernel .sendWorker pid)).wp (fun t => t=s)
  have hm := (modifyDev_words (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}) (fun _ => rfl)).wp (fun t => t=s)
  mvcgen [sendQueuedHandshakeInitiation,hs,hg,hp,ht,hr,hm,requireNotPending,getPeer,getDev,getK,branch,invariant]
  all_goals try simp_all [keyWords]

theorem keyUpdate_protect (id : KeypairId) (f : Keypair → Keypair) :
    SameView protectView (do let k ← getKeypair id; setKeypair id (f k)) := by
  have hg : SameView protectView (getKeypair id) := by
    apply SameView.of_wp
    intro s
    mvcgen [getKeypair,getDev,getK,invariant]
  apply SameView.bind hg
  intro k
  exact modifyDev_protect _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem keyUpdate_compatible (pid kid target : Nat) (f : Keypair → Keypair)
    (hf : ∀k, Affiliation.keyCell (f k) = Affiliation.keyCell k) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ (do let k ← getKeypair target; setKeypair target (f k))
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  simp only [compatible_factor]
  have hg := Affiliation.getKeypair_spec (compatibleState pid kid) target
  have hs := fun k => Affiliation.setKeypair_spec (compatibleState pid kid) target (f k)
  mvcgen [hg,hs]
  all_goals simp_all [hf]

theorem transfer_getPeer (initial : World) (pid : PeerId) :
    ⦃fun w => ⌜Transfer initial w⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜Transfer initial w ∧ protectPeerAt w pid = some (protectCell p)⌝⦄ := by
  mvcgen [getPeer,getDev,getK,invariant]
  all_goals simp_all [protectPeerAt]

theorem transfer_setPeer (initial : World) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜Transfer initial w ∧ protectPeerAt w pid = some (protectCell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  have he := (hoare_iff_triple _ _ _).mpr (setPeer_protect_spec (fun t => t=protectView w) pid p) w x v ⟨rfl,h.2⟩ hr
  exact h.1.after_view he

theorem setKeypair_protect (id : KeypairId) (k : Keypair) : SameView protectView (setKeypair id k) :=
  modifyDev_protect _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem stagedOutNokey_transfers (pid : PeerId) (packets : List WG.Packet) (kp : Option KeypairId) (invalid : Bool) :
    Transfers (Lifetimes.stagedOutNokey pid packets kp invalid) := by
  intro w x v hr
  have spec : ⦃fun u => ⌜Transfer w u⌝⦄ Lifetimes.stagedOutNokey pid packets kp invalid
      ⦃⇓? _ u => ⌜Transfer w u⌝⦄ := by
    have hg := transfer_getPeer w pid
    have hs := fun p => transfer_setPeer w pid p
    have hk := fun id k => transfer_frame (setKeypair_protect id k) w
    have hp := fun key => transfer_frame (keypairPut_protect key false) w
    have hq := (sendQueued_transfers pid false).wp w
    have hb := branch_predicate (Transfer w) (transfer_stable w)
    have hl (α β : Type) := list_view_spec (fun w : World => w) (α:=α) (β:=β) (Transfer w)
    simp only [Lifetimes.stagedOutNokey,getPeer_twice]
    mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,hg,hs,hk,hp,hq,hb,getKeypair,getDev,getK,invariant]
    all_goals try exact ((⇓? _ u => ⌜Transfer w u⌝) : PostCond _ (.arg World (.except Stop .pure)))
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [protectCell]
  exact (hoare_iff_triple _ _ _).mpr spec w x v (Transfer.refl w) hr

theorem stagedOutNokey_compatible (pid kid : Nat) (packets : List WG.Packet) (kp : Option KeypairId) (invalid : Bool) :
    ⦃fun w => ⌜KeyCompatible pid kid w⌝⦄ Lifetimes.stagedOutNokey pid packets kp invalid
    ⦃⇓? _ w => ⌜KeyCompatible pid kid w⌝⦄ := by
  have hg := fun id => Affiliation.getKeypair_spec (compatibleState pid kid) id
  have hs := fun id k => Affiliation.setKeypair_spec (compatibleState pid kid) id k
  have hp := fun key => keypairPut_compatible pid kid key false
  have hq := keyWords_keep (queued_words pid false) pid kid
  have hpeer := fun p => setPeer_compatible pid kid pid p
  have hl (α β : Type) := list_view_spec (fun w : World => w) (α:=α) (β:=β) (KeyCompatible pid kid)
  simp only [Lifetimes.stagedOutNokey,getPeer_twice]
  simp only [← compatible_factor] at hg hs
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,hg,hs,hp,hq,hpeer,getPeer,getDev,getK,branch,invariant]
  all_goals try exact ((⇓? _ u => ⌜KeyCompatible pid kid u⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Affiliation.keyCell,KeyCompatible]

def StageInv (initial : World) (pid kid : Nat) (w : World) := Transfer initial w ∧ KeyCompatible pid kid w

theorem stage_kernel (ha : SameKernel a) (initial : World) (pid kid : Nat) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ a ⦃⇓? _ w => ⌜StageInv initial pid kid w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  refine ⟨h.1.after_view (protect_kernel ha w x v hr),?_⟩
  simpa [KeyCompatible,ha w x v hr] using h.2

theorem stage_getKey (initial : World) (pid kid target : Nat) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ getKeypair target
    ⦃⇓? k w => ⌜StageInv initial pid kid w ∧ Affiliation.keyAt w target = some (Affiliation.keyCell k)⌝⦄ := by
  mvcgen [getKeypair,getDev,getK,invariant]
  all_goals simp_all [Affiliation.keyAt]

theorem stage_setKey (initial : World) (pid kid target : Nat) (k : Keypair) :
    ⦃fun w => ⌜StageInv initial pid kid w ∧ Affiliation.keyAt w target = some (Affiliation.keyCell k)⌝⦄ setKeypair target k
    ⦃⇓? _ w => ⌜StageInv initial pid kid w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  refine ⟨h.1.1.after_view (setKeypair_protect target k w x v hr),?_⟩
  rw [compatible_factor]
  exact (hoare_iff_triple _ _ _).mpr (Affiliation.setKeypair_spec (compatibleState pid kid) target k)
    w x v ⟨compatible_factor.mp h.1.2,h.2⟩ hr

theorem stage_outNokey (initial : World) (pid kid : Nat) (packets : List WG.Packet) (kp : Option KeypairId) (invalid : Bool) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ Lifetimes.stagedOutNokey pid packets kp invalid
    ⦃⇓? _ w => ⌜StageInv initial pid kid w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  exact ⟨h.1.trans (stagedOutNokey_transfers pid packets kp invalid w x v hr),
    (hoare_iff_triple _ _ _).mpr (stagedOutNokey_compatible pid kid packets kp invalid) w x v h.2 hr⟩

def stagedSubmit (pid kid : Nat) (packets : List DataPacket) : M Unit := do
  Affiliation.sendAcquire kid
  let item ← packets.mapM newTxSkb
  createData pid item

theorem stage_submit (initial : World) (pid kid : Nat) (packets : List DataPacket) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ stagedSubmit pid kid packets
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  exact h.1.trans (stagedSubmit_handoff packets h.2 hr)

/-- Literal continuation after the optional current-key get. -/
def stagedKeySource (pid kid : Nat) (packets : List WG.Packet) : M Unit := do
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

theorem stagedKeySource_spec (initial : World) (pid kid : Nat) (packets : List WG.Packet) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ stagedKeySource pid kid packets
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  have hg := stage_getKey initial pid kid kid
  have hs := stage_setKey initial pid kid kid
  have ho := stage_outNokey initial pid kid packets (some kid)
  have hb := fun decision value => stage_kernel (sameKernel_branch decision value) initial pid kid
  have hc := fun decision value a b => stage_kernel (branchCmp_sameKernel decision value a b) initial pid kid
  have ht := fun date => stage_kernel (branchExpired_sameKernel .stagedBirthdateExpired date REJECT_AFTER_TIME) initial pid kid
  have he := fun pkt => stage_kernel (Lifetimes.ipTunnelEcnEncap_sameKernel pkt) initial pid kid
  have hsub := stage_submit initial pid kid
  have hl (α β : Type) := list_view_spec (fun w : World => w) (α:=α) (β:=β) (StageInv initial pid kid)
  mvcgen [stagedKeySource,-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,hg,hs,ho,hb,hc,ht,he,hsub]
  all_goals try exact ((⇓? _ u => ⌜StageInv initial pid kid u⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [StageInv,Affiliation.keyCell]

def SelectInv (initial : World) (pid : PeerId) (kp : Option KeypairId) (w : World) : Prop :=
  Transfer initial w ∧ ∀kid, kp = some kid → KeyCompatible pid kid w

def SelectPending (initial : World) (pid : PeerId) (p : Peer) (w : World) : Prop :=
  SelectInv initial pid p.keypairCurrent w ∧ protectPeerAt w pid = some (protectCell p)

theorem select_stable (initial : World) (pid : PeerId) (kp : Option KeypairId) : KernelStable (SelectInv initial pid kp) := by
  intro w v hk h
  exact ⟨transfer_stable initial w v hk h.1,by simpa [KeyCompatible,hk] using h.2⟩
theorem selectPending_stable (initial : World) (pid : PeerId) (p : Peer) : KernelStable (SelectPending initial pid p) := by
  intro w v hk h
  exact ⟨select_stable initial pid p.keypairCurrent w v hk h.1,by simpa [protectPeerAt,hk] using h.2⟩

theorem select_getPeer (initial : World) (pid : PeerId) :
    ⦃fun w => ⌜Transfer initial w ∧ CurrentCompatible pid w⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜SelectPending initial pid p w⌝⦄ := by
  mvcgen [getPeer,getDev,getK,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [SelectPending,SelectInv,protectPeerAt,CurrentCompatible]
  all_goals grind

theorem select_setPeer (initial : World) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜SelectPending initial pid p w⌝⦄ setPeer pid {p with staged:=[]}
    ⦃⇓? _ w => ⌜SelectInv initial pid p.keypairCurrent w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  refine ⟨(hoare_iff_triple _ _ _).mpr (transfer_setPeer initial pid {p with staged:=[]}) w x v ⟨h.1.1,h.2⟩ hr,?_⟩
  intro kid hk
  exact (hoare_iff_triple _ _ _).mpr (setPeer_compatible pid kid pid {p with staged:=[]}) w x v (h.1.2 kid hk) hr

theorem select_keyGet (initial : World) (pid : PeerId) (kp : Option KeypairId) :
    ⦃fun w => ⌜SelectInv initial pid kp w⌝⦄ keypairGet kp
    ⦃⇓? result w => ⌜SelectInv initial pid result w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w result v h hr
  have hf := (hoare_iff_triple _ _ _).mpr (Affiliation.keypairGet_affiliation kp (Affiliation.view w)) w result v rfl hr
  refine ⟨h.1.after_view (keypairGet_protect kp w result v hr),?_⟩
  intro kid hk
  have he : kp=some kid := by rcases hf.2 with hh|hh <;> simp_all
  rw [compatible_factor,hf.1]
  exact compatible_factor.mp (h.2 kid he)

def stagedFullSource (pid : PeerId) : M Unit := do
  let p ← getPeer pid
  if ← branch .stagedEmpty p.staged.isEmpty then return
  setPeer pid {p with staged:=[]}
  let kp ← keypairGet p.keypairCurrent
  if ← branch .stagedNoKeypair kp.isNone then return ← Lifetimes.stagedOutNokey pid p.staged kp false
  let some kid := kp | invariant "unreachable"
  stagedKeySource pid kid p.staged

theorem bind_congr_source (a : M α) (f g : α → M β) (h : ∀x,f x=g x) : a >>= f = a >>= g := by
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
    (hr : (sendStagedPackets pid).run w = .ok ((),v)) : Transfer w v := by
  have spec : ⦃fun u => ⌜Transfer w u ∧ CurrentCompatible pid u⌝⦄ stagedFullSource pid
      ⦃⇓? _ u => ⌜Transfer w u⌝⦄ := by
    have hg := select_getPeer w pid
    have hb := fun p => branch_predicate (SelectPending w pid p) (selectPending_stable w pid p) .stagedEmpty p.staged.isEmpty
    have hs := select_setPeer w pid
    have hk := select_keyGet w pid
    have hn := fun kp => branch_predicate (SelectInv w pid kp) (select_stable w pid kp) .stagedNoKeypair kp.isNone
    have ho := fun packets kp => (stagedOutNokey_transfers pid packets kp false).wp w
    have ht := stagedKeySource_spec w pid
    mvcgen [stagedFullSource,hg,hb,hs,hk,hn,ho,ht,invariant]
    all_goals simp_all [SelectPending,SelectInv,StageInv]
  exact (hoare_iff_triple _ _ _).mpr spec w () v ⟨Transfer.refl w,hc⟩ (by simpa [stagedFullSource_eq] using hr)

def currentKey (w : World) : PeerId → Option KeypairId :=
  fun pid => (w.k.wg.bind fun d => d.peers[pid]?).bind (·.keypairCurrent)
def controlView (w : World) := (protectView w,currentKey w,keyWords w)
def controlCell (p : Peer) := (protectCell p,p.keypairCurrent)
def controlAt (w : World) (pid : PeerId) := (w.k.wg.bind fun d => d.peers[pid]?).map controlCell

theorem control_kernel (ha : SameKernel a) : SameView controlView a := by
  intro w x v hr
  unfold controlView protectView peerView rxView handoffTxView sendView currentKey keyWords
  rw [ha w x v hr]

theorem control_getPeer (P : _ → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (controlView w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P (controlView w) ∧ controlAt w pid = some (controlCell p)⌝⦄ := by
  mvcgen [getPeer,getDev,getK,invariant]
  all_goals simp_all [controlAt]

theorem control_set_same (hd : w.k.wg = some d) (hp : d.peers[pid]? = some old)
    (hc : controlCell p = controlCell old) :
    controlView {w with k := {w.k with wg := some {d with peers:=d.peers.insert pid p}}} = controlView w := by
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
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  cases hd : w.k.wg with
  | none => simp [controlAt,hd] at h
  | some d =>
    obtain ⟨old,hp,hc⟩ := Option.map_eq_some_iff.mp (by simpa [controlAt,hd] using h.2)
    cases hr
    simpa [setPeer,modifyDev,modifyK,hd,control_set_same hd hp hc.symm] using h.1

theorem control_protect (h : SameView controlView a) : SameView protectView a :=
  fun w x v hr => congrArg Prod.fst (h w x v hr)
theorem control_words (h : SameView controlView a) : SameView keyWords a :=
  fun w x v hr => congrArg (fun t => t.2.2) (h w x v hr)

theorem current_factor : CurrentCompatible pid w ↔ ∀kid,currentKey w pid=some kid → KeyCompatible pid kid w := by
  constructor
  · intro h kid hk
    obtain ⟨p,hp,hkey⟩ := Option.bind_eq_some_iff.mp hk
    obtain ⟨d,hd,hslot⟩ := Option.bind_eq_some_iff.mp hp
    exact h d p kid hd hslot hkey
  · intro h d p kid hd hp hk
    exact h kid (by simp [currentKey,hd,hp,hk])

theorem control_current (h : SameView controlView a) (pid : PeerId) :
    ⦃fun w => ⌜CurrentCompatible pid w⌝⦄ a ⦃⇓? _ w => ⌜CurrentCompatible pid w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  rw [current_factor] at hi ⊢
  have he := h w x v hr
  have hw : currentKey v = currentKey w := congrArg (fun t => t.2.1) he
  have hk : keyWords v = keyWords w := congrArg (fun t => t.2.2) he
  intro kid hc
  rw [hw] at hc
  rw [compatible_words]
  simpa only [hk] using compatible_words.mp (hi kid hc)

theorem delTimer_control (pid : PeerId) (t : PeerTimer) : SameView controlView (delTimer pid t) := by
  apply SameView.of_wp
  intro s
  have hg := control_getPeer (fun v => v=s) pid
  have hs := fun p => control_setPeer (fun v => v=s) pid p
  mvcgen [delTimer,hg,hs]
  all_goals cases t <;> simp_all [controlCell,protectCell,Peer.setTimer]

theorem armTimer_control (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64) : SameView controlView (armTimer pid t delay jc) := by
  apply SameView.of_wp
  intro s
  have hg := control_getPeer (fun v => v=s) pid
  have hs := fun p => control_setPeer (fun v => v=s) pid p
  have hh := (control_kernel (hidden_sameKernel .modTimerArm)).wp (fun v => v=s)
  mvcgen [armTimer,hg,hs,hh,branch,branchCmp,unsupported,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals cases t <;> simp_all [controlCell,protectCell,Peer.setTimer]

theorem modPeerTimer_control (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    SameView controlView (modPeerTimer site pid t delay) := by
  apply SameView.of_wp
  intro s
  have hj := (control_kernel (callerJiffies_sameKernel site)).wp (fun v => v=s)
  have ha := fun jc => (armTimer_control pid t delay jc).wp (fun v => v=s)
  mvcgen [modPeerTimer,modPeerTimerGuard,WG.andM,hj,ha,getPeer,getDev,getK,branch,invariant]

theorem timersHandshakeComplete_control (pid : PeerId) (site : HiddenSite) :
    SameView controlView (timersHandshakeComplete pid site) := by
  apply SameView.of_wp
  intro s
  have hg := control_getPeer (fun v => v=s) pid
  have hs := fun p => control_setPeer (fun v => v=s) pid p
  have hd := (delTimer_control pid .retransmitHandshake).wp (fun v => v=s)
  have hh := (control_kernel (hidden_sameKernel site)).wp (fun v => v=s)
  mvcgen [timersHandshakeComplete,hg,hs,hd,hh]
  all_goals simp_all [controlCell,protectCell]

theorem timersDataReceived_control (pid : PeerId) : SameView controlView (timersDataReceived pid) := by
  apply SameView.of_wp
  intro s
  have hg := control_getPeer (fun v => v=s) pid
  have hs := fun p => control_setPeer (fun v => v=s) pid p
  have ht := (modPeerTimer_control .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp (fun v => v=s)
  have hd := discard_view_spec controlView (fun v => v=s) _ ht
  have hb := fun d b => (control_kernel (sameKernel_branch d b)).wp (fun v => v=s)
  mvcgen [timersDataReceived,hg,hs,ht,hd,hb,getDev,getK,invariant]
  all_goals simp_all [controlCell,protectCell]

theorem timersTraversal_control (pid : PeerId) : SameView controlView (timersTraversal pid) := by
  apply SameView.of_wp
  intro s
  have ht := fun n => (modPeerTimer_control .timerJiffiesTraversal pid .persistentKeepalive n).wp (fun v => v=s)
  have hd := fun n => discard_view_spec controlView (fun v => v=s) _ (ht n)
  mvcgen [timersTraversal,ht,hd,getPeer,getDev,getK,branchCmp,invariant]

theorem dstCacheReset_control (pid : PeerId) : SameView controlView (dstCacheReset pid) := by
  apply SameView.of_wp
  intro s
  have hg := control_getPeer (fun v => v=s) pid
  have hs := fun p => control_setPeer (fun v => v=s) pid p
  have hh := (control_kernel (hiddenJiffies_sameKernel .dstCacheResetTs)).wp (fun v => v=s)
  mvcgen [dstCacheReset,hg,hs,hh]
  all_goals simp_all [controlCell,protectCell]

theorem setPeerEndpoint_control (pid : PeerId) (e : Endpoint) : SameView controlView (setPeerEndpoint pid e) := by
  apply SameView.of_wp
  intro s
  have hg := control_getPeer (fun v => v=s) pid
  have hs := fun p => control_setPeer (fun v => v=s) pid p
  have he := fun old => (control_kernel (Lifetimes.endpointEq_sameKernel e old)).wp (fun v => v=s)
  have hc := (dstCacheReset_control pid).wp (fun v => v=s)
  have hb := fun d b => (control_kernel (sameKernel_branch d b)).wp (fun v => v=s)
  mvcgen [setPeerEndpoint,hg,hs,he,hc,hb,requireNotPending]
  all_goals simp_all [controlCell,protectCell]

theorem updateRxStats_protect (pid : PeerId) (len : Nat) : SameView protectView (updateRxStats pid len) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_protect_spec (fun v => v=s) pid
  have hs := fun p => setPeer_protect_spec (fun v => v=s) pid p
  have hm := (modifyDev_protect (fun d => {d with rxPackets:=d.rxPackets+1,rxBytes:=d.rxBytes+len})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun v => v=s)
  mvcgen [updateRxStats,hg,hs,hm]
  all_goals simp_all [protectCell]

theorem dishonest_protect (why : Dishonest) : SameView protectView (dishonest why) :=
  modifyDev_protect _ (fun _ => by cases why <;> rfl) (fun _ => by cases why <;> rfl)
    (fun _ => by cases why <;> rfl) (fun _ => by cases why <;> rfl)

theorem keepKeyFreshRx_transfers (pid : PeerId) : Transfers (keepKeyFreshRx pid) := by
  intro w x v hr
  have spec : ⦃fun u => ⌜Transfer w u⌝⦄ keepKeyFreshRx pid ⦃⇓? _ u => ⌜Transfer w u⌝⦄ := by
    have hg := transfer_getPeer w pid
    have hs := transfer_setPeer w pid
    have ht := fun date delay => transfer_frame (protect_kernel (branchExpired_sameKernel .rxFreshExpired date delay)) w
    have hq := (sendQueued_transfers pid false).wp w
    have hb := branch_predicate (Transfer w) (transfer_stable w)
    mvcgen [keepKeyFreshRx,hg,hs,ht,hq,hb,WG.andM,getKeypair,getDev,getK,invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [protectCell]
  exact (hoare_iff_triple _ _ _).mpr spec w x v (Transfer.refl w) hr

theorem stage_control (ha : SameView controlView a) (initial : World) (pid kid : Nat) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ a ⦃⇓? _ w => ⌜StageInv initial pid kid w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  exact ⟨h.1.after_view (control_protect ha w x v hr),
    (hoare_iff_triple _ _ _).mpr (keyWords_keep (control_words ha) pid kid) w x v h.2 hr⟩

def AfterPromotion (initial : World) (pid : PeerId) (newKey : Bool) (w : World) :=
  Transfer initial w ∧ (newKey=true → CurrentCompatible pid w)

theorem afterPromotion_stable (initial : World) (pid : PeerId) (newKey : Bool) :
    KernelStable (AfterPromotion initial pid newKey) := by
  intro w v hk h
  exact ⟨transfer_stable initial w v hk h.1,by simpa [CurrentCompatible,KeyCompatible,hk] using h.2⟩

theorem receivedWithKeypair_prepare (initial : World) (pid kid : Nat) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ receivedWithKeypair pid kid
    ⦃⇓? result w => ⌜AfterPromotion initial pid result w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w result v h hr
  refine ⟨h.1.after_view (receivedWithKeypair_protect pid kid w result v hr),?_⟩
  intro he; subst result
  exact receivedWithKeypair_current_compatible h.2 hr

theorem current_control (ha : SameView controlView a) (initial : World) (pid : PeerId) :
    ⦃fun w => ⌜Transfer initial w ∧ CurrentCompatible pid w⌝⦄ a
    ⦃⇓? _ w => ⌜Transfer initial w ∧ CurrentCompatible pid w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  exact ⟨h.1.after_view (control_protect ha w x v hr),
    (hoare_iff_triple _ _ _).mpr (control_current ha pid) w x v h.2 hr⟩

theorem staged_send_spec (initial : World) (pid : PeerId) :
    ⦃fun w => ⌜Transfer initial w ∧ CurrentCompatible pid w⌝⦄ sendStagedPackets pid
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  exact h.1.trans (staged_send_handoff pid h.2 hr)

def promoteAndSend (pid kid : Nat) : M Unit := do
  if ← branch .doneReceivedNew (← receivedWithKeypair pid kid) then
    timersHandshakeComplete pid .walltimeLastHandshakeData
    sendStagedPackets pid

theorem promoteAndSend_transfer (initial : World) (pid kid : Nat) :
    ⦃fun w => ⌜StageInv initial pid kid w⌝⦄ promoteAndSend pid kid
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  have hk := receivedWithKeypair_prepare initial pid kid
  have hb := fun b => branch_predicate (AfterPromotion initial pid b) (afterPromotion_stable initial pid b) .doneReceivedNew b
  have hh := current_control (timersHandshakeComplete_control pid .walltimeLastHandshakeData) initial pid
  have hs := staged_send_spec initial pid
  mvcgen [promoteAndSend,hk,hb,hh,hs]
  all_goals simp_all [AfterPromotion]

def prepareRest (pid : PeerId) (pkt : RxPacket) : M (Option Packets.RxReady) := do
  keepKeyFreshRx pid
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  let bytes := pkt.bytes
  let len := bytes.length   -- skb->len
  let reject (why : Dishonest) : M (Option Packets.RxReady) := do
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

theorem prepareRest_transfer (initial : World) (pid : PeerId) (pkt : RxPacket) :
    ⦃fun w => ⌜Transfer initial w⌝⦄ prepareRest pid pkt
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  have hf := (keepKeyFreshRx_transfers pid).wp initial
  have ha := transfer_frame (control_protect (delTimer_control pid .newHandshake)) initial
  have ht := transfer_frame (control_protect (timersTraversal_control pid)) initial
  have hd := transfer_frame (control_protect (timersDataReceived_control pid)) initial
  have hstat := fun len => transfer_frame (updateRxStats_protect pid len) initial
  have he := fun why => transfer_frame (dishonest_protect why) initial
  have hecn := fun proto outer bytes => transfer_frame (protect_kernel (Lifetimes.inetEcnDecapsulate_sameKernel proto outer bytes)) initial
  have hbranch := fun d b => branch_predicate (Transfer initial) (transfer_stable initial) d b
  mvcgen [prepareRest,timersAnyAuthenticatedPacketReceived,hf,ha,ht,hd,hstat,he,hecn,hbranch,WG.andM,WG.orM]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem rxPrepare_transfer (initial : World) (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    ⦃fun w => ⌜StageInv initial pid pkt.keypair w⌝⦄ Packets.rxPrepare pid pkt endpoint
    ⦃⇓? _ w => ⌜Transfer initial w⌝⦄ := by
  rw [rxPrepare_factor]
  have he := stage_control (setPeerEndpoint_control pid endpoint) initial pid pkt.keypair
  have hp := promoteAndSend_transfer initial pid pkt.keypair
  have hr := prepareRest_transfer initial pid pkt
  mvcgen [he,hp,hr]

def protectionOfBorrow (s : Kernel × (PeerId → Option Peer)) :=
  ((s.1.wg.map (·.ifindex),fun pid => (s.2 pid).map fun p => (p.internalId,p.refcount,p.rxQueue)),
   (s.1.wg.map (·.ifindex),fun (id : SkbId) => s.1.wg.bind fun d => d.rxSkbs[id]?),
   (fun pid => (s.2 pid).map fun p => p.txQueue.all),s.1.wg.map (·.sendWorkQueue))

theorem protection_borrow_factor (w : World) : protectView w = protectionOfBorrow (PeerBorrow.view w) := by
  unfold protectView protectionOfBorrow PeerBorrow.view PeerBorrow.outsidePeers PeerBorrow.resident
    peerView rxView handoffTxView sendView
  cases hd : w.k.wg <;> simp [hd]

theorem lookupRepay_protect (protocol : Nat) (bytes : List UInt8) :
    SameView protectView (RxBorrow.source protocol bytes) :=
  (RxBorrow.source_frame protocol bytes).of_factor protectionOfBorrow protectView protection_borrow_factor

def rxFinishSource (pid : PeerId) (ready : Packets.RxReady) : M (Option (List UInt8)) := do
  let routed ← RxBorrow.source ready.protocol ready.bytes
  if ← branch .doneDishonestPeer (routed != some pid) then
    dishonest .peer
    return none
  updateRxStats pid (ready.originalLen + MESSAGE_DATA_LEN_0)
  return some (ready.bytes.take ready.ipLen)

theorem rxFinishSource_eq (pid : PeerId) (ready : Packets.RxReady) : rxFinishSource pid ready = Packets.rxFinish pid ready := by
  simp only [rxFinishSource,Packets.rxFinish,Packets.rxAfterLookup,RxBorrow.source,RxBorrow.repayLookup,bind_assoc,pure_bind]

theorem rxFinish_protect (pid : PeerId) (ready : Packets.RxReady) : SameView protectView (Packets.rxFinish pid ready) := by
  rw [← rxFinishSource_eq]
  apply SameView.of_wp
  intro s
  have hl := (lookupRepay_protect ready.protocol ready.bytes).wp (fun v => v=s)
  have hd := (dishonest_protect .peer).wp (fun v => v=s)
  have hs := (updateRxStats_protect pid (ready.originalLen+MESSAGE_DATA_LEN_0)).wp (fun v => v=s)
  have hb := fun d b => (protect_kernel (sameKernel_branch d b)).wp (fun v => v=s)
  mvcgen [rxFinishSource,hl,hd,hs,hb]

/-- Full original callback on its normal endpoints. The only owner hypothesis
is the packet key's nullable word compatibility at entry. -/
theorem consumeDataDone_handoff (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (hc : KeyCompatible pid pkt.keypair w)
    (hr : (consumeDataDone pid pkt endpoint).run w = .ok (result,v)) : Transfer w v := by
  have spec : ⦃fun u => ⌜StageInv w pid pkt.keypair u⌝⦄ consumeDataDone pid pkt endpoint
      ⦃⇓? _ u => ⌜Transfer w u⌝⦄ := by
    rw [Packets.consumeDataDone_factor]
    have hp := rxPrepare_transfer w pid pkt endpoint
    have hf := fun ready => transfer_frame (rxFinish_protect pid ready) w
    mvcgen [hp,hf]
  exact (hoare_iff_triple _ _ _).mpr spec w result v ⟨Transfer.refl w,hc⟩ hr

end Leanux.Proofs.WG.Queues.RxCredits
