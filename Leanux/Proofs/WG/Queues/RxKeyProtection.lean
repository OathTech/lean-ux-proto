import Leanux.Proofs.WG.Queues.RxConsumeProtection
import Leanux.Proofs.WG.Queues.RxStackFrames

/-! Nullable owner-word and current-slot effects of the actual callback paths.
These are normal-endpoint contracts. Deletion is permitted, and no World is
assigned to a stopped computation. The product deliberately omits validity,
key material, allocation frontiers and unrelated previous/next slots. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
set_option pp.structureInstances false

def currentCell (p : Peer) := (p.internalId,p.keypairCurrent)
def currentCells (w : World) : PeerId → Option (Nat × Option KeypairId) :=
  fun pid => (w.k.wg.bind fun d => d.peers[pid]?).map currentCell
def keyView (w : World) := (w.k.wg.map (·.ifindex),keyWords w,currentCells w)

/-- Every surviving current cell, including a resident `current = none`, has
the same device epoch and peer stamp as its source. Only the named source
promotion may replace its current slot. Non-NULL key words cannot be invented. -/
abbrev KeyView := Option Nat × (KeypairId → Option (Option PeerId)) × (PeerId → Option (Nat × Option KeypairId))
structure KeyRelation (allowed : PeerId → KeypairId → Prop) (w v : KeyView) : Prop where
  epoch : v.1 = w.1
  words : ∀ kid pid, v.2.1 kid = some (some pid) → w.2.1 kid = some (some pid)
  currents : ∀ pid stamp current, v.2.2 pid = some (stamp,current) →
    ∃ old, w.2.2 pid = some (stamp,old) ∧
      (current = old ∨ ∃ kid, current = some kid ∧ allowed pid kid)
abbrev KeyEffect (allowed : PeerId → KeypairId → Prop) (w v : World) :=
  KeyRelation allowed (keyView w) (keyView v)

def NoPromotion (_ : PeerId) (_ : KeypairId) : Prop := False
def ReceivedPromotion (pid : PeerId) (kid : KeypairId) (q : PeerId) (k : KeypairId) : Prop :=
  q = pid ∧ k = kid

theorem KeyEffect.refl (allowed) (w : World) : KeyEffect allowed w w :=
  ⟨rfl,fun _ _ h => h,fun _ _ current h => ⟨current,h,Or.inl rfl⟩⟩

theorem KeyEffect.trans (h : KeyEffect allowed w u) (j : KeyEffect allowed u v) :
    KeyEffect allowed w v := by
  refine ⟨j.epoch.trans h.epoch,fun k p hp => h.words k p (j.words k p hp),?_⟩
  intro pid stamp current hc
  obtain ⟨middle,hm,he⟩ := j.currents pid stamp current hc
  obtain ⟨old,ho,hf⟩ := h.currents pid stamp middle hm
  refine ⟨old,ho,?_⟩
  rcases he with rfl | he
  · exact hf
  · exact Or.inr he

theorem KeyEffect.mono (h : KeyEffect a w v) (imp : ∀p k,a p k → b p k) : KeyEffect b w v := by
  refine ⟨h.epoch,h.words,?_⟩
  intro p s c hc
  obtain ⟨old,ho,he⟩ := h.currents p s c hc
  exact ⟨old,ho,he.imp id (fun ⟨k,hk,ha⟩ => ⟨k,hk,imp p k ha⟩)⟩

theorem keyEffect_of_view (h : keyView v = keyView w) : KeyEffect allowed w v := by
  refine ⟨congrArg Prod.fst h,?_,?_⟩
  · intro k p hp
    exact (congrFun (congrArg (fun x => x.2.1) h) k).symm.trans hp
  · intro p s c hc
    exact ⟨c,(congrFun (congrArg (fun x => x.2.2) h) p).symm.trans hc,Or.inl rfl⟩

abbrev KeyEffects (allowed : PeerId → KeypairId → Prop) (a : M α) :=
  ∀ w x v, a.run w = .ok (x,v) → KeyEffect allowed w v

theorem KeyEffects.wp (ha : KeyEffects allowed a) (initial : World) :
    ⦃fun w => ⌜KeyEffect allowed initial w⌝⦄ a
    ⦃⇓? _ w => ⌜KeyEffect allowed initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v h hr
  exact h.trans (ha w x v hr)

theorem keyEffects_of_wp {a : M α} (h : ∀initial, ⦃fun w => ⌜KeyEffect allowed initial w⌝⦄ a
    ⦃⇓? _ w => ⌜KeyEffect allowed initial w⌝⦄) : KeyEffects allowed a := by
  intro w x v hr
  exact (hoare_iff_triple _ _ _).mpr (h w) w x v (KeyEffect.refl _ _) hr

theorem keyView_kernel (ha : SameKernel a) : SameView keyView a := by
  intro w x v hr
  unfold keyView keyWords currentCells
  rw [ha w x v hr]

theorem keyEffects_view (ha : SameView keyView a) : KeyEffects allowed a :=
  fun w x v hr => keyEffect_of_view (ha w x v hr)

theorem keyEffect_stable (allowed) (initial : World) : KernelStable (KeyEffect allowed initial) := by
  intro w v hk h
  exact h.trans (keyEffect_of_view (by unfold keyView keyWords currentCells; rw [hk]))

theorem modifyDev_keyView (f : Device → Device)
    (he : ∀d,(f d).ifindex=d.ifindex) (hp : ∀d,(f d).peers=d.peers)
    (hk : ∀d,(f d).keypairs=d.keypairs) : SameView keyView (modifyDev f) := by
  intro w x v hr
  cases hr
  unfold keyView keyWords currentCells
  simp [modifyDev,modifyK,Option.map_map,Option.bind_map,Function.comp_def,he,hp,hk]

theorem getPeer_key_spec (P : _ → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (keyView w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P (keyView w) ∧ currentCells w pid = some (currentCell p)⌝⦄ := by
  mvcgen [getPeer,getDev,getK,invariant]
  all_goals simp_all [currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

theorem keyView_set_peer (hd : w.k.wg=some d) (hp : d.peers[pid]?=some old)
    (hc : currentCell p=currentCell old) :
    keyView {w with k:={w.k with wg:=some {d with peers:=d.peers.insert pid p}}}=keyView w := by
  unfold keyView keyWords currentCells
  simp only [hd,Option.map_some,Option.bind_some]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext q
  by_cases h : pid=q <;> simp_all [Std.TreeMap.getElem?_insert]

theorem setPeer_key_spec (P : _ → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (keyView w) ∧ currentCells w pid=some (currentCell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜P (keyView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  cases hd : w.k.wg with
  | none => simp [keyView,currentCells,hd] at hi
  | some d =>
    obtain ⟨old,hp,hc⟩ := Option.map_eq_some_iff.mp (by simpa [keyView,currentCells,hd] using hi.2)
    cases hr
    simpa [setPeer,modifyDev,modifyK,hd,keyView_set_peer hd hp hc.symm] using hi.1

theorem getPeer_effect (allowed) (initial : World) (pid : PeerId) :
    ⦃fun w => ⌜KeyEffect allowed initial w⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜KeyEffect allowed initial w ∧ currentCells w pid=some (currentCell p)⌝⦄ := by
  mvcgen [getPeer,getDev,getK,invariant]
  all_goals simp_all [currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

theorem setPeer_effect (allowed) (initial : World) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜KeyEffect allowed initial w ∧ currentCells w pid=some (currentCell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜KeyEffect allowed initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  have he := (hoare_iff_triple _ _ _).mpr (setPeer_key_spec (fun t => t=keyView w) pid p) w x v ⟨rfl,hi.2⟩ hr
  exact hi.1.trans (keyEffect_of_view he)

def stateKeyView (s : Option Affiliation.State) : KeyView :=
  (s.map (·.epoch),fun k => (s.bind fun t => t.keys k).map Prod.snd,
    fun p => (s.bind fun t => t.peers p).map fun c => (c.1,c.2.2.1))

theorem keyView_factor (w : World) : keyView w=stateKeyView (Affiliation.view w) := by
  cases hd : w.k.wg <;>
    simp [keyView,stateKeyView,Affiliation.view,Affiliation.state,keyWords,currentCells,
      Affiliation.peerCell,Affiliation.keyCell,Option.map_map,Function.comp_def,currentCell,hd]
  all_goals constructor <;> funext q <;> simp [keyWords,currentCells,currentCell,hd]
  all_goals rfl

theorem keyView_affiliation (h : Affiliation.view v = Affiliation.view w) : keyView v=keyView w := by
  rw [keyView_factor,keyView_factor,h]

theorem keypairGet_keyView (kp : Option KeypairId) : SameView keyView (keypairGet kp) := by
  intro w x v hr
  exact keyView_affiliation ((hoare_iff_triple _ _ _).mpr (Affiliation.keypairGet_affiliation kp (Affiliation.view w)) w x v rfl hr).1

theorem keyUpdate_keyView (id : KeypairId) (f : Keypair → Keypair)
    (hf : ∀k,Affiliation.keyCell (f k)=Affiliation.keyCell k) :
    SameView keyView (do let k ← getKeypair id; setKeypair id (f k)) := by
  intro w x v hr
  have spec : ⦃fun u => ⌜Affiliation.view u=Affiliation.view w⌝⦄
      (do let k ← getKeypair id; setKeypair id (f k))
      ⦃⇓? _ u => ⌜Affiliation.view u=Affiliation.view w⌝⦄ := by
    have hg := Affiliation.getKeypair_spec (fun t => t=Affiliation.view w) id
    have hs := fun k => Affiliation.setKeypair_spec (fun t => t=Affiliation.view w) id (f k)
    mvcgen [hg,hs]
    all_goals simpa [hf]
  exact keyView_affiliation ((hoare_iff_triple _ _ _).mpr spec w x v rfl hr)

theorem erasePeer_effect (pid : PeerId) (f : Device → Device)
    (he : ∀d,(f d).ifindex=d.ifindex) (hp : ∀d,(f d).peers=d.peers.erase pid)
    (hk : ∀d,(f d).keypairs=d.keypairs) : KeyEffects allowed (modifyDev f) := by
  intro w x v hr
  cases hr
  constructor
  · simp [keyView,modifyDev,modifyK,Option.map_map,Function.comp_def,he]
  · intro k p h
    simpa [keyView,keyWords,modifyDev,modifyK,Option.bind_map,Function.comp_def,hk] using h
  · intro q s c h
    cases hd : w.k.wg with
    | none => simp [keyView,currentCells,modifyDev,modifyK,hd] at h
    | some d =>
      have ne : pid≠q := by intro eq; simp [keyView,currentCells,modifyDev,modifyK,hd,hp,eq] at h
      refine ⟨c,?_,Or.inl rfl⟩
      simpa [keyView,currentCells,modifyDev,modifyK,hd,hp,Std.TreeMap.getElem?_erase,ne] using h

theorem peerGet_keyView (pid : PeerId) : SameView keyView (peerGet pid) := by
  intro w x v hr
  cases x
  obtain ⟨d,p,hd,hp,pos,hv⟩ :=
    (hoare_iff_triple _ _ _).mpr (PeerBorrow.strict_acquire_spec pid w.k) w () v rfl hr
  apply keyView_affiliation
  simp only [Affiliation.view,hv,hd,Option.map_some]
  exact congrArg some (Affiliation.state_peer_same d pid p {p with refcount:=p.refcount+1} hp rfl)

theorem peerPut_keyEffect (pid : Option PeerId) : KeyEffects allowed (peerPut pid) := by
  apply keyEffects_of_wp
  intro initial
  have hg := fun p => getPeer_effect allowed initial p
  have hs := fun p q => setPeer_effect allowed initial p q
  have hi := fun o => (keyEffects_view (allowed:=allowed) (fun w x v hr => keyView_affiliation (Affiliation.index_frame (indexRemove_sameIndexKernel o) w x v hr))).wp initial
  have hc := fun n => (keyEffects_view (allowed:=allowed) (keyView_kernel (refcountDecAndTest_sameKernel n))).wp initial
  have he := fun pid len => (erasePeer_effect (allowed:=allowed) pid (fun d => {d with txDropped:=d.txDropped+len,peers:=d.peers.erase pid})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp initial
  have ht := fun pid => (keyEffects_view (allowed:=allowed) (keyView_kernel (show SameKernel (retirePeerUnits pid) from fun _ _ _ h => by cases h; rfl))).wp initial
  have hb := branch_predicate (KeyEffect allowed initial) (keyEffect_stable _ _)
  mvcgen [peerPut,hg,hs,hi,hc,he,ht,hb,requireNotPending,invariant]
  all_goals simp_all [currentCell]

theorem getKey_effect (allowed) (initial : World) (kid : KeypairId) :
    ⦃fun w => ⌜KeyEffect allowed initial w⌝⦄ getKeypair kid
    ⦃⇓? k w => ⌜KeyEffect allowed initial w ∧ Affiliation.keyAt w kid=some (Affiliation.keyCell k)⌝⦄ := by
  mvcgen [getKeypair,getDev,getK,invariant]
  all_goals simp_all [Affiliation.keyAt]

theorem setKey_effect (allowed) (initial : World) (kid : KeypairId) (k : Keypair) :
    ⦃fun w => ⌜KeyEffect allowed initial w ∧ Affiliation.keyAt w kid=some (Affiliation.keyCell k)⌝⦄ setKeypair kid k
    ⦃⇓? _ w => ⌜KeyEffect allowed initial w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hi hr
  have he := (hoare_iff_triple _ _ _).mpr (Affiliation.setKeypair_spec (fun t => t=Affiliation.view w) kid k) w x v ⟨rfl,hi.2⟩ hr
  exact hi.1.trans (keyEffect_of_view (keyView_affiliation he))

theorem eraseKey_effect (kid : KeypairId) :
    KeyEffects allowed (modifyDev fun d => {d with keypairs:=d.keypairs.erase kid}) := by
  intro w x v hr
  cases hr
  constructor
  · simp [keyView,modifyDev,modifyK,Option.map_map,Function.comp_def]
  · intro k p h
    cases hd : w.k.wg with
    | none => simp [keyView,keyWords,modifyDev,modifyK,hd] at h
    | some d =>
      by_cases he : kid=k
      · simp [keyView,keyWords,modifyDev,modifyK,hd,he] at h
      · simpa [keyView,keyWords,modifyDev,modifyK,hd,Std.TreeMap.getElem?_erase,he] using h
  · intro p s c h
    exact ⟨c,by simpa [keyView,currentCells,modifyDev,modifyK,Option.bind_map,Function.comp_def] using h,Or.inl rfl⟩

theorem keypairPut_keyEffect (kp : Option KeypairId) (now : Bool) : KeyEffects allowed (keypairPut kp now) := by
  intro w x v hr
  let P := fun s => KeyRelation allowed (keyView w) (stateKeyView s)
  have closed : ∀s kid,P (some s) → P (some (s.eraseKey kid)) := by
    intro s kid h
    refine ⟨h.epoch,?_,h.currents⟩
    intro k pid hk
    by_cases he : k=kid
    · simp [stateKeyView,Affiliation.State.eraseKey,he] at hk
    · exact h.words k pid (by simpa [stateKeyView,Affiliation.State.eraseKey,he] using hk)
  have hi : P (Affiliation.view w) := by simpa [P,←keyView_factor] using KeyEffect.refl allowed w
  have result := (hoare_iff_triple _ _ _).mpr (Affiliation.keypairPut_affiliation P closed kp now) w x v hi hr
  simpa [P,←keyView_factor] using result

theorem control_keyView (he : controlView v=controlView w) : keyView v=keyView w := by
  refine Prod.ext (congrArg (fun s => s.1.1.1) he) (Prod.ext (congrArg (fun s => s.2.2) he) ?_)
  funext pid
  have hp := congrFun (congrArg (fun s => s.1.1.2) he) pid
  have hc := congrFun (congrArg (fun s => s.2.1) he) pid
  simp only [controlView,protectView,peerView,currentKey] at hp hc
  change (v.k.wg.bind fun d => d.peers[pid]?).map currentCell = (w.k.wg.bind fun d => d.peers[pid]?).map currentCell
  cases hv : (v.k.wg.bind fun d => d.peers[pid]?) <;>
    cases hw : (w.k.wg.bind fun d => d.peers[pid]?) <;> simp_all [currentCell]

theorem control_keyEffects (ha : SameView controlView a) : KeyEffects allowed a :=
  keyEffects_view (fun w x v hr => control_keyView (ha w x v hr))

theorem modifyPeer_keyView (pid : PeerId) (f : Peer → Peer)
    (hf : ∀p,currentCell (f p)=currentCell p) :
    SameView keyView ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by
  change SameView keyView (do let p ← getPeer pid; setPeer pid (f p))
  apply SameView.of_wp
  intro s
  have hg := getPeer_key_spec (fun t => t=s) pid
  have hs := fun p => setPeer_key_spec (fun t => t=s) pid (f p)
  mvcgen [hg,hs]
  all_goals simpa [hf]

theorem promotion_effect (pid kid : Nat) :
    KeyEffects (ReceivedPromotion pid kid)
      ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairCurrent:=some kid,keypairNext:=none})) := by
  intro w x v hr
  change (do let p ← getPeer pid; setPeer pid {p with keypairCurrent:=some kid,keypairNext:=none}).run w = .ok (x,v) at hr
  cases hd : w.k.wg with
  | none => simp [getPeer,getDev,getK,hd,invariant] at hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [getPeer,getDev,getK,hd,hp,invariant] at hr
    | some p =>
      simp [getPeer,getDev,getK,hd,hp,setPeer,modifyDev,modifyK] at hr
      obtain ⟨rfl,rfl⟩ := hr
      refine ⟨by simp [keyView,hd],?_,?_⟩
      · intro k q h; simpa [keyView,keyWords,hd] using h
      · intro q st cur h
        by_cases hq : pid=q
        · subst q
          simp [keyView,currentCells,currentCell] at h
          obtain ⟨rfl,rfl⟩ := h
          exact ⟨p.keypairCurrent,by simp [keyView,currentCells,currentCell,hd,hp],Or.inr ⟨kid,rfl,rfl,rfl⟩⟩
        · exact ⟨cur,by simpa [keyView,currentCells,hd,Std.TreeMap.getElem?_insert,hq] using h,Or.inl rfl⟩

theorem receivedWithKeypair_keyEffect (pid kid : Nat) :
    KeyEffects (ReceivedPromotion pid kid) (receivedWithKeypair pid kid) := by
  apply keyEffects_of_wp
  intro initial
  have hk := fun old => (keypairPut_keyEffect (allowed:=ReceivedPromotion pid kid) old true).wp initial
  have hm := (keyEffects_view (allowed:=ReceivedPromotion pid kid)
    (modifyPeer_keyView pid (fun p => {p with keypairPrevious:=p.keypairCurrent}) (fun _ => rfl))).wp initial
  have hs := (promotion_effect pid kid).wp initial
  mvcgen [receivedWithKeypair,hk,hm,hs,getPeer,getDev,getK,branch,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [KeyEffect,keyWords,currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

/-- Resident RX cells require only nullable ownership of their actual key. -/
def RxCompatible (w : World) : Prop := ∀(d : Device) (id : SkbId) (pkt : RxPacket),
  w.k.wg=some d → d.rxSkbs[id]?=some pkt → KeyCompatible pkt.peer pkt.keypair w
def CurrentsCompatible (w : World) : Prop := ∀pid,CurrentCompatible pid w
def KeysCompatible (w : World) : Prop := RxCompatible w ∧ CurrentsCompatible w

theorem KeyEffect.compatible (h : KeyEffect allowed w v) (hc : KeyCompatible pid kid w) : KeyCompatible pid kid v := by
  rw [compatible_words] at hc ⊢
  intro word hw
  cases word with
  | none => exact Or.inl rfl
  | some owner => exact hc _ (h.words kid owner hw)

theorem KeyEffect.currentsCompatible (h : KeyEffect allowed w v) (hc : CurrentsCompatible w)
    (ha : ∀pid kid,allowed pid kid → KeyCompatible pid kid w) : CurrentsCompatible v := by
  intro pid d p kid hd hp hk
  have cell : currentCells v pid=some (p.internalId,some kid) := by simp [keyView,currentCells,currentCell,hd,hp,hk]
  obtain ⟨old,ho,he⟩ := h.currents pid p.internalId (some kid) cell
  apply h.compatible
  rcases he with he | ⟨k,hk,allowed⟩
  · rw [← he] at ho
    obtain ⟨op,hop,hcell⟩ := Option.map_eq_some_iff.mp ho
    obtain ⟨od,hod,hopp⟩ := Option.bind_eq_some_iff.mp hop
    exact hc pid od op kid hod hopp (congrArg Prod.snd hcell)
  · cases hk; exact ha pid kid allowed

theorem KeyEffect.rxCompatible (h : KeyEffect allowed w v) (hrx : rxView v=rxView w)
    (hc : RxCompatible w) : RxCompatible v := by
  intro d id pkt hd hp
  have slots := congrFun (congrArg Prod.snd hrx) id
  have old : (w.k.wg.bind fun d => d.rxSkbs[id]?)=some pkt := by simpa [rxView,hd,hp] using slots.symm
  obtain ⟨od,hod,hp⟩ := Option.bind_eq_some_iff.mp old
  exact h.compatible (hc od id pkt hod hp)

theorem getTx_keyView (id : SkbId) : SameView keyView (getTxSkb id) := by
  apply SameView.of_wp; intro s
  mvcgen [getTxSkb,getDev,getK,invariant]

theorem setTx_keyView (id : SkbId) (f : DataPacket → DataPacket) : SameView keyView (setTxSkb id f) := by
  apply SameView.of_wp; intro s
  have hg := (getTx_keyView id).wp (fun t => t=s)
  have hm := fun p => (modifyDev_keyView (fun d => {d with txSkbs:=d.txSkbs.insert id (f p)})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  mvcgen [setTxSkb,hg,hm]

theorem freeTx_keyView (id : SkbId) : SameView keyView (freeTxSkb id) := by
  apply SameView.of_wp; intro s
  have hg := (getTx_keyView id).wp (fun t => t=s)
  have hm := (modifyDev_keyView (fun d => {d with txSkbs:=d.txSkbs.erase id})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  mvcgen [freeTxSkb,hg,hm]

theorem newTx_keyView (pkt : DataPacket) : SameView keyView (newTxSkb pkt) := by
  apply SameView.of_wp; intro s
  have hm := fun (d : Device) => (modifyDev_keyView (fun v => {v with
    nextSkb:=d.nextSkb+1,txSkbs:=v.txSkbs.insert d.nextSkb pkt})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  mvcgen [newTxSkb,hm,getDev,getK,invariant]

theorem newTxList_keyView (packets : List DataPacket) : SameView keyView (packets.mapM newTxSkb) := by
  induction packets with
  | nil => exact SameView.pure _ _
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact (newTx_keyView p).bind fun _ => ih.bind fun _ => SameView.pure _ _

theorem cpu_keyView (pid : PeerId) : SameView keyView (cpumaskChooseOnline pid) := by
  apply SameView.of_wp; intro s
  have hg := getPeer_key_spec (fun t => t=s) pid
  have hs := fun p => setPeer_key_spec (fun t => t=s) pid p
  simp only [cpumaskChooseOnline,Nat.mod_one]
  mvcgen [hg,hs,branch]
  all_goals try exact ((⇓? _ w => ⌜keyView w=s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [currentCell,keyView,keyWords,currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

theorem enqueue_keyView (pid : PeerId) (item : List SkbId) : SameView keyView (enqueuePerDeviceAndPeer pid item) := by
  apply SameView.of_wp; intro s
  have hg := getPeer_key_spec (fun t => t=s) pid
  have hs := fun p => setPeer_key_spec (fun t => t=s) pid p
  have ht := fun id f => (setTx_keyView id f).wp (fun t => t=s)
  have hc := fun last => (keyView_kernel (Lifetimes.cpumaskNextOnlineFrom_sameKernel last)).wp (fun t => t=s)
  have hw := (keyView_kernel (Lifetimes.queueDeviceWork_sameKernel .encryptWorker)).wp (fun t => t=s)
  have hd := fun (u : Lifetimes.TxDeviceUpdate) => (modifyDev_keyView u.apply
    (fun d => by cases u <;> rfl) (fun d => by cases u <;> rfl) (fun d => by cases u <;> rfl)).wp (fun t => t=s)
  have hcpu := fun cpu => hd (.cpu cpu)
  have hring := hd (.ring item)
  mvcgen [enqueuePerDeviceAndPeer,hg,hs,ht,hc,hw,hcpu,hring,getDev,getK,modifyDev,modifyK,branch,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [currentCell,keyView,keyWords,currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

theorem publication_keyEffect (item : List SkbId) (state : PacketState) :
    KeyEffects allowed (enqueuePerPeerTx item state) := by
  apply keyEffects_of_wp; intro initial
  have hg := getPeer_effect allowed initial
  have ht := fun id => (keyEffects_view (allowed:=allowed) (getTx_keyView id)).wp initial
  have hp := fun pid => (keyEffects_view (allowed:=allowed) (peerGet_keyView pid)).wp initial
  have hf := fun pid => (peerPut_keyEffect (allowed:=allowed) pid).wp initial
  have hs := fun id f => (keyEffects_view (allowed:=allowed) (setTx_keyView id f)).wp initial
  have hc := fun pid => (keyEffects_view (allowed:=allowed) (cpu_keyView pid)).wp initial
  have hk := fun o => (keyEffects_view (allowed:=allowed) (keyView_kernel (indexOwner_peerDeref_sameKernel o))).wp initial
  have hpeek := fun pid => (keyEffects_view (allowed:=allowed) (keyView_kernel (peekQueuedUnit_sameKernel .txWorker pid))).wp initial
  have hrec := fun pid => (keyEffects_view (allowed:=allowed) (keyView_kernel (Lifetimes.recordQueued_sameKernel .txWorker pid))).wp initial
  have hm := fun pid => (keyEffects_view (allowed:=allowed) (modifyDev_keyView
    (fun d => {d with txWorkQueue:=d.txWorkQueue++[pid]}) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))).wp initial
  mvcgen [enqueuePerPeerTx,hg,ht,hp,hf,hs,hc,hk,hpeek,hrec,hm,getDev,getK,branch,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [KeyEffect,keyView,keyWords,currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

theorem createData_keyEffect (pid : PeerId) (item : List SkbId) : KeyEffects allowed (createData pid item) := by
  apply keyEffects_of_wp; intro initial
  have hd := (keyEffects_view (allowed:=allowed) (enqueue_keyView pid item)).wp initial
  have hp := (publication_keyEffect (allowed:=allowed) item .dead).wp initial
  have hk := fun id => (keypairPut_keyEffect (allowed:=allowed) id false).wp initial
  have hr := (peerPut_keyEffect (allowed:=allowed) (some pid)).wp initial
  have hf := fun id => (keyEffects_view (allowed:=allowed) (freeTx_keyView id)).wp initial
  have ht := fun id => (keyEffects_view (allowed:=allowed) (getTx_keyView id)).wp initial
  mvcgen [createData,hd,hp,hk,hr,hf,ht,getPeer,getDev,getK,branch,invariant]
  all_goals try exact ((⇓? _ w => ⌜KeyEffect allowed initial w⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [KeyEffect,keyView,keyWords,currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

theorem queued_keyEffect (pid : PeerId) (retry : Bool) : KeyEffects allowed (sendQueuedHandshakeInitiation pid retry) := by
  apply keyEffects_of_wp; intro initial
  have hg := getPeer_effect allowed initial pid
  have hs := fun p => setPeer_effect allowed initial pid p
  have hp := (keyEffects_view (allowed:=allowed) (peerGet_keyView pid)).wp initial
  have hf := (peerPut_keyEffect (allowed:=allowed) (some pid)).wp initial
  have ht := fun date => (keyEffects_view (allowed:=allowed) (keyView_kernel (branchExpired_sameKernel .queuedNotExpired date REKEY_TIMEOUT (!·)))).wp initial
  have hr := (keyEffects_view (allowed:=allowed) (keyView_kernel (Lifetimes.recordQueued_sameKernel .sendWorker pid))).wp initial
  have hm := (keyEffects_view (allowed:=allowed) (modifyDev_keyView
    (fun d => {d with sendWorkQueue:=d.sendWorkQueue++[pid]}) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))).wp initial
  mvcgen [sendQueuedHandshakeInitiation,hg,hs,hp,hf,ht,hr,hm,requireNotPending,branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [currentCell,KeyEffect,keyView,keyWords,currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

theorem stagedOutNokey_keyEffect (pid : PeerId) (packets : List WG.Packet) (kp : Option KeypairId) (invalid : Bool) :
    KeyEffects allowed (Lifetimes.stagedOutNokey pid packets kp invalid) := by
  apply keyEffects_of_wp; intro initial
  have hg := getPeer_effect allowed initial pid
  have hs := setPeer_effect allowed initial pid
  have hk := getKey_effect allowed initial
  have hset := setKey_effect allowed initial
  have hp := fun key => (keypairPut_keyEffect (allowed:=allowed) key false).wp initial
  have hq := (queued_keyEffect (allowed:=allowed) pid false).wp initial
  have hl (α β : Type) := list_view_spec keyView (α:=α) (β:=β) (KeyRelation allowed (keyView initial))
  simp only [Lifetimes.stagedOutNokey,getPeer_twice]
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,hg,hs,hk,hset,hp,hq,branch,invariant]
  all_goals try exact ((⇓? _ w => ⌜KeyEffect allowed initial w⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [currentCell,Affiliation.keyCell,KeyEffect,keyView,keyWords,currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

theorem stagedSubmit_keyEffect (pid kid : Nat) (packets : List DataPacket) : KeyEffects allowed (stagedSubmit pid kid packets) := by
  apply keyEffects_of_wp; intro initial
  have ho := (keyEffects_view (allowed:=allowed) (keyView_kernel (indexOwner_peerDeref_sameKernel (.keypair kid)))).wp initial
  have hp := fun pid => (keyEffects_view (allowed:=allowed) (peerGet_keyView pid)).wp initial
  have hn := (keyEffects_view (allowed:=allowed) (newTxList_keyView packets)).wp initial
  have hc := fun item => (createData_keyEffect (allowed:=allowed) pid item).wp initial
  mvcgen [stagedSubmit,Affiliation.sendAcquire,ho,hp,hn,hc]

theorem stagedKeySource_keyEffect (pid kid : Nat) (packets : List WG.Packet) :
    KeyEffects allowed (stagedKeySource pid kid packets) := by
  apply keyEffects_of_wp; intro initial
  have hg := getKey_effect allowed initial kid
  have hs := setKey_effect allowed initial kid
  have ho := fun invalid => (stagedOutNokey_keyEffect (allowed:=allowed) pid packets (some kid) invalid).wp initial
  have ht := fun date => (keyEffects_view (allowed:=allowed) (keyView_kernel (branchExpired_sameKernel .stagedBirthdateExpired date REJECT_AFTER_TIME))).wp initial
  have he := fun pkt => (keyEffects_view (allowed:=allowed) (keyView_kernel (Lifetimes.ipTunnelEcnEncap_sameKernel pkt))).wp initial
  have hsub := fun ps => (stagedSubmit_keyEffect (allowed:=allowed) pid kid ps).wp initial
  have hl (α β : Type) := list_view_spec keyView (α:=α) (β:=β) (KeyRelation allowed (keyView initial))
  mvcgen [stagedKeySource,-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,hg,hs,ho,ht,he,hsub,branch,branchCmp]
  all_goals try exact ((⇓? _ w => ⌜KeyEffect allowed initial w⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Affiliation.keyCell,KeyEffect,keyView,keyWords,currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

theorem staged_send_keyEffect (pid : PeerId) : KeyEffects allowed (sendStagedPackets pid) := by
  rw [←stagedFullSource_eq]
  apply keyEffects_of_wp; intro initial
  have hg := getPeer_effect allowed initial pid
  have hs := setPeer_effect allowed initial pid
  have hk := fun kp => (keyEffects_view (allowed:=allowed) (keypairGet_keyView kp)).wp initial
  have ho := fun packets kp => (stagedOutNokey_keyEffect (allowed:=allowed) pid packets kp false).wp initial
  have hc := fun kid packets => (stagedKeySource_keyEffect (allowed:=allowed) pid kid packets).wp initial
  mvcgen [stagedFullSource,hg,hs,hk,ho,hc,branch,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [currentCell,KeyEffect,keyView,keyWords,currentCells]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell,Affiliation.keyCell,Option.map_map,Option.bind_map,Function.comp_def])

theorem updateRxStats_keyView (pid : PeerId) (len : Nat) : SameView keyView (updateRxStats pid len) := by
  apply SameView.of_wp; intro s
  have hg := getPeer_key_spec (fun t => t=s) pid
  have hs := fun p => setPeer_key_spec (fun t => t=s) pid p
  have hm := (modifyDev_keyView (fun d => {d with rxPackets:=d.rxPackets+1,rxBytes:=d.rxBytes+len})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t=s)
  mvcgen [updateRxStats,hg,hs,hm]
  all_goals simp_all [currentCell]

theorem dishonest_keyView (why : Dishonest) : SameView keyView (dishonest why) :=
  modifyDev_keyView _ (fun _ => by cases why <;> rfl) (fun _ => by cases why <;> rfl) (fun _ => by cases why <;> rfl)

theorem keepKeyFreshRx_keyEffect (pid : PeerId) : KeyEffects allowed (keepKeyFreshRx pid) := by
  apply keyEffects_of_wp; intro initial
  have hg := getPeer_effect allowed initial pid
  have hs := setPeer_effect allowed initial pid
  have ht := fun date delay => (keyEffects_view (allowed:=allowed) (keyView_kernel (branchExpired_sameKernel .rxFreshExpired date delay))).wp initial
  have hq := (queued_keyEffect (allowed:=allowed) pid false).wp initial
  have hb := branch_predicate (KeyEffect allowed initial) (keyEffect_stable _ _)
  mvcgen [keepKeyFreshRx,hg,hs,ht,hq,hb,getKeypair,getDev,getK,WG.andM,invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [currentCell,KeyEffect,keyView]
  all_goals try (unfold keyWords currentCells at *; simp_all [currentCell])

theorem promoteAndSend_keyEffect (pid kid : Nat) :
    KeyEffects (ReceivedPromotion pid kid) (promoteAndSend pid kid) := by
  apply keyEffects_of_wp; intro initial
  have hp := (receivedWithKeypair_keyEffect pid kid).wp initial
  have ht := (control_keyEffects (allowed:=ReceivedPromotion pid kid)
    (timersHandshakeComplete_control pid .walltimeLastHandshakeData)).wp initial
  have hs := (staged_send_keyEffect (allowed:=ReceivedPromotion pid kid) pid).wp initial
  mvcgen [promoteAndSend,hp,ht,hs,branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [KeyEffect,keyView]
  all_goals try (unfold keyWords currentCells at *; simp_all)

theorem prepareRest_keyEffect (pid : PeerId) (pkt : RxPacket) : KeyEffects allowed (prepareRest pid pkt) := by
  apply keyEffects_of_wp; intro initial
  have hf := (keepKeyFreshRx_keyEffect (allowed:=allowed) pid).wp initial
  have ha := (control_keyEffects (allowed:=allowed) (delTimer_control pid .newHandshake)).wp initial
  have ht := (control_keyEffects (allowed:=allowed) (timersTraversal_control pid)).wp initial
  have hd := (control_keyEffects (allowed:=allowed) (timersDataReceived_control pid)).wp initial
  have hs := fun len => (keyEffects_view (allowed:=allowed) (updateRxStats_keyView pid len)).wp initial
  have he := fun why => (keyEffects_view (allowed:=allowed) (dishonest_keyView why)).wp initial
  have hc := fun proto outer bytes => (keyEffects_view (allowed:=allowed)
    (keyView_kernel (Lifetimes.inetEcnDecapsulate_sameKernel proto outer bytes))).wp initial
  have hb := branch_predicate (KeyEffect allowed initial) (keyEffect_stable _ _)
  mvcgen [prepareRest,timersAnyAuthenticatedPacketReceived,hf,ha,ht,hd,hs,he,hc,hb,WG.andM,WG.orM]
  all_goals simp_all

def keyViewOfBorrow (s : Kernel × (PeerId → Option Peer)) : KeyView :=
  (s.1.wg.map (·.ifindex),fun kid => (s.1.wg.bind fun d => d.keypairs[kid]?).map (·.peer),
    fun pid => (s.2 pid).map currentCell)

theorem keyView_borrow_factor (w : World) : keyView w=keyViewOfBorrow (PeerBorrow.view w) := by
  unfold keyView keyViewOfBorrow keyWords currentCells PeerBorrow.view PeerBorrow.outsidePeers PeerBorrow.resident
  cases hd : w.k.wg <;> simp [hd]

theorem lookupRepay_keyView (protocol : Nat) (bytes : List UInt8) : SameView keyView (RxBorrow.source protocol bytes) :=
  (RxBorrow.source_frame protocol bytes).of_factor keyViewOfBorrow keyView keyView_borrow_factor

theorem rxFinish_keyView (pid : PeerId) (ready : Packets.RxReady) : SameView keyView (Packets.rxFinish pid ready) := by
  rw [←rxFinishSource_eq]
  apply SameView.of_wp; intro s
  have hl := (lookupRepay_keyView ready.protocol ready.bytes).wp (fun t => t=s)
  have hd := (dishonest_keyView .peer).wp (fun t => t=s)
  have hs := (updateRxStats_keyView pid (ready.originalLen+MESSAGE_DATA_LEN_0)).wp (fun t => t=s)
  have hb := fun d b => (keyView_kernel (sameKernel_branch d b)).wp (fun t => t=s)
  mvcgen [rxFinishSource,hl,hd,hs,hb]

/-- Unconditional normal source effect: only this actual received key can
become the target's new current key. It says nothing about material identity. -/
theorem consumeDataDone_keyEffect (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    KeyEffects (ReceivedPromotion pid pkt.keypair) (consumeDataDone pid pkt endpoint) := by
  apply keyEffects_of_wp; intro initial
  rw [Packets.consumeDataDone_factor,rxPrepare_factor]
  have he := (control_keyEffects (allowed:=ReceivedPromotion pid pkt.keypair) (setPeerEndpoint_control pid endpoint)).wp initial
  have hp := (promoteAndSend_keyEffect pid pkt.keypair).wp initial
  have hr := (prepareRest_keyEffect (allowed:=ReceivedPromotion pid pkt.keypair) pid pkt).wp initial
  have hf := fun ready => (keyEffects_view (allowed:=ReceivedPromotion pid pkt.keypair) (rxFinish_keyView pid ready)).wp initial
  mvcgen [he,hp,hr,hf]

theorem staged_send_keys (pid : PeerId) (hi : KeysCompatible w)
    (hr : (sendStagedPackets pid).run w=.ok ((),v)) : KeysCompatible v := by
  have effect := staged_send_keyEffect (allowed:=NoPromotion) pid w () v hr
  obtain ⟨delta,handoff⟩ := staged_send_handoff pid (hi.2 pid) hr
  exact ⟨effect.rxCompatible handoff.rx hi.1,
    effect.currentsCompatible hi.2 (fun _ _ h => False.elim h)⟩

theorem consumeDataDone_keys (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (hi : KeysCompatible w) (hc : KeyCompatible pid pkt.keypair w)
    (hr : (consumeDataDone pid pkt endpoint).run w=.ok (result,v)) : KeysCompatible v := by
  have effect := consumeDataDone_keyEffect pid pkt endpoint w result v hr
  obtain ⟨delta,handoff⟩ := consumeDataDone_handoff pid pkt endpoint hc hr
  refine ⟨effect.rxCompatible handoff.rx hi.1,effect.currentsCompatible hi.2 ?_⟩
  intro q k h
  rcases h with ⟨rfl,rfl⟩
  exact hc

end Leanux.Proofs.WG.Queues.RxCredits
