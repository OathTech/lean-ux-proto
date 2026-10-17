import Leanux.Proofs.WG.Queues.RxConsumeProtection
import Leanux.Proofs.WG.Queues.RxStackFrames

/-! Nullable owner-word and current-slot effects of the actual callback paths.
These are normal-endpoint contracts. Deletion is permitted, and no World is
assigned to a stopped computation. The product deliberately omits validity,
key material, allocation frontiers and unrelated previous/next slots. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
set_option pp.structureInstances false

def currentCell (p : Peer) := (p.internalId,p.keypairCurrent)
def currentCells (w : WGWorld) : PeerId → Option (Nat × Option KeypairId) :=
  fun pid => (w.dev.bind fun d => d.peers[pid]?).map currentCell
def keyView (w : WGWorld) := (w.dev.map (·.ifindex),keyWords w,currentCells w)

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
abbrev KeyEffect (allowed : PeerId → KeypairId → Prop) (w v : WGWorld) :=
  KeyRelation allowed (keyView w) (keyView v)

def NoPromotion (_ : PeerId) (_ : KeypairId) : Prop := False
def ReceivedPromotion (pid : PeerId) (kid : KeypairId) (q : PeerId) (k : KeypairId) : Prop :=
  q = pid ∧ k = kid

theorem KeyEffect.refl (allowed) (w : WGWorld) : KeyEffect allowed w w :=
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

abbrev ProjectedKeyEffects {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (project : S → WGWorld)
    (allowed : PeerId → KeypairId → Prop) (a : StateT S m α) : Prop :=
  ProjectedAction project (KeyEffect allowed) a

abbrev KeyEffects (allowed : PeerId → KeypairId → Prop) (a : WG.M α) : Prop :=
  ProjectedKeyEffects id allowed a
abbrev ProductKeyEffects (allowed : PeerId → KeypairId → Prop) (a : Leanux.M α) : Prop :=
  ProjectedKeyEffects World.wg allowed a

theorem KeyEffects.iff_run_ambient (allowed) (a : WG.M α) :
    KeyEffects allowed a ↔ ∀ w ambient x v ambient',
      (a.run w).run ambient = .ok ((x,v),ambient') → KeyEffect allowed w v :=
  ProjectedAction.iff_run_ambient id (KeyEffect allowed) a

theorem ProductKeyEffects.iff_run (allowed) (a : Leanux.M α) :
    ProductKeyEffects allowed a ↔ ∀ w x v,
      a.run w = .ok (x,v) → KeyEffect allowed w.wg v.wg :=
  ProjectedAction.iff_run World.wg (KeyEffect allowed) a

/-- Callback contracts retain arbitrary actual-state scope, including the product. -/
theorem KeyEffects.wp {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : ProjectedKeyEffects project allowed a) (initial : WGWorld) :
    ⦃fun w => ⌜KeyEffect allowed initial (project w)⌝⦄ a
    ⦃⇓? _ w => ⌜KeyEffect allowed initial (project w)⌝⦄ :=
  ProjectedAction.wp ha (KeyEffect allowed initial)
    (fun _ _ step before => before.trans step)

theorem keyEffects_of_wp {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : ∀ initial, ⦃fun w => ⌜KeyEffect allowed initial (project w)⌝⦄ a
      ⦃⇓? _ w => ⌜KeyEffect allowed initial (project w)⌝⦄) :
    ProjectedKeyEffects project allowed a := by
  intro initial
  apply hoare_consequence (h initial)
  · intro w he; rw [he]; exact KeyEffect.refl _ _
  · exact fun _ _ hi => hi

theorem keyView_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => keyView (project w)) a :=
  ha.of_factor (fun store : WGStoreView =>
    (store.dev.map (·.ifindex),fun kid => (store.dev.bind fun d => d.keypairs[kid]?).map (·.peer),
      fun pid => (store.dev.bind fun d => d.peers[pid]?).map currentCell)) _ (fun _ => rfl)

theorem keyEffects_view {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => keyView (project w)) a) :
    ProjectedKeyEffects project allowed a := by
  intro initial
  apply hoare_consequence
    (ha.wp (fun obs => ∃ w, w = initial ∧ obs = keyView w))
  · intro w hi; exact ⟨project w,hi,rfl⟩
  · intro x w hi
    obtain ⟨old,rfl,he⟩ := hi
    exact keyEffect_of_view he

theorem keyEffect_stable (allowed) (initial : WGWorld) : WGStoreStable (KeyEffect allowed initial) := by
  intro w v hk h
  exact h.trans (keyEffect_of_view (by
    have hd : v.dev = w.dev := congrArg WGStoreView.dev hk
    unfold keyView keyWords currentCells
    rw [hd]))

theorem modifyDev_keyView (f : Device → Device)
    (he : ∀d,(f d).ifindex=d.ifindex) (hp : ∀d,(f d).peers=d.peers)
    (hk : ∀d,(f d).keypairs=d.keypairs) : SameView keyView (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  unfold keyView keyWords currentCells
  simp [Option.map_map,Option.bind_map,Function.comp_def,he,hp,hk]

theorem getPeer_key_spec (P : _ → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (keyView w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P (keyView w) ∧ currentCells w pid = some (currentCell p)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hi hr
  obtain ⟨rfl,_,d,hd,hp⟩ := getPeer_normal pid w v p ambient ambient' hr
  exact ⟨hi,by simp [currentCells,hd,hp]⟩

theorem keyView_set_peer (hd : w.dev=some d) (hp : d.peers[pid]?=some old)
    (hc : currentCell p=currentCell old) :
    keyView {w with dev:=some {d with peers:=d.peers.insert pid p}}=keyView w := by
  unfold keyView keyWords currentCells
  simp only [hd,Option.map_some,Option.bind_some]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext q
  by_cases h : pid=q <;> simp_all [Std.TreeMap.getElem?_insert]

theorem setPeer_key_spec (P : _ → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (keyView w) ∧ currentCells w pid=some (currentCell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜P (keyView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  cases hd : w.dev with
  | none => simp [currentCells,hd] at hi
  | some d =>
    obtain ⟨old,hp,hc⟩ := Option.map_eq_some_iff.mp (by simpa [currentCells,hd] using hi.2)
    cases hr
    simpa [hd,keyView_set_peer hd hp hc.symm] using hi.1

theorem getPeer_effect (allowed) (initial : WGWorld) (pid : PeerId) :
    ⦃fun w => ⌜KeyEffect allowed initial w⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜KeyEffect allowed initial w ∧ currentCells w pid=some (currentCell p)⌝⦄ :=
  getPeer_key_spec (KeyRelation allowed (keyView initial)) pid

theorem setPeer_effect (allowed) (initial : WGWorld) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜KeyEffect allowed initial w ∧ currentCells w pid=some (currentCell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜KeyEffect allowed initial w⌝⦄ :=
  setPeer_key_spec (KeyRelation allowed (keyView initial)) pid p

def stateKeyView (s : Option Affiliation.State) : KeyView :=
  (s.map (·.epoch),fun k => (s.bind fun t => t.keys k).map Prod.snd,
    fun p => (s.bind fun t => t.peers p).map fun c => (c.1,c.2.2.1))

theorem keyView_factor (w : WGWorld) : keyView w=stateKeyView (Affiliation.view w) := by
  cases hd : w.dev <;>
    simp [keyView,stateKeyView,Affiliation.view,Affiliation.state,
      Affiliation.peerCell,Affiliation.keyCell,Option.map_map,Function.comp_def,hd]
  all_goals constructor <;> funext q <;> simp [keyWords,currentCells,hd]
  all_goals rfl

theorem keyView_affiliation (h : Affiliation.view v = Affiliation.view w) : keyView v=keyView w := by
  rw [keyView_factor,keyView_factor,h]

theorem keypairGet_keyView (kp : Option KeypairId) : SameView keyView (keypairGet kp) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  exact keyView_affiliation
    ((hoare_iff_run_ambient _ _ _).mp
      (Affiliation.keypairGet_affiliation kp (Affiliation.view w))
      w ambient x v ambient' rfl hr).1

theorem keyUpdate_keyView (id : KeypairId) (f : Keypair → Keypair)
    (hf : ∀k,Affiliation.keyCell (f k)=Affiliation.keyCell k) :
    SameView keyView (do let k ← getKeypair id; setKeypair id (f k)) := by
  intro initial
  let P := fun obs => ∃ w, obs = Affiliation.view w ∧ keyView w = initial
  have action : Hoare (do let k ← getKeypair id; setKeypair id (f k))
      (fun w => P (Affiliation.view w)) (fun _ w => P (Affiliation.view w)) := by
    apply hoare_bind _ _ (Affiliation.getKeypair_spec P id)
    intro k
    apply hoare_consequence (Affiliation.setKeypair_spec P id (f k))
    · intro w hi; exact ⟨hi.1,by simpa [hf] using hi.2⟩
    · exact fun _ _ hi => hi
  apply hoare_consequence action
  · intro w hi; exact ⟨w,rfl,hi⟩
  · intro x v hi
    obtain ⟨w,hv,he⟩ := hi
    exact (keyView_affiliation hv).trans he

theorem erasePeer_effect (pid : PeerId) (f : Device → Device)
    (he : ∀d,(f d).ifindex=d.ifindex) (hp : ∀d,(f d).peers=d.peers.erase pid)
    (hk : ∀d,(f d).keypairs=d.keypairs) : KeyEffects allowed (modifyDev f) := by
  apply (KeyEffects.iff_run_ambient _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  constructor
  · simp [keyView,Option.map_map,Function.comp_def,he]
  · intro k p h
    simpa [keyView,keyWords,Option.bind_map,Function.comp_def,hk] using h
  · intro q s c h
    cases hd : w.dev with
    | none => simp [keyView,currentCells,hd] at h
    | some d =>
      have ne : pid≠q := by intro eq; simp [keyView,currentCells,hd,hp,eq] at h
      refine ⟨c,?_,Or.inl rfl⟩
      simpa [keyView,currentCells,hd,hp,Std.TreeMap.getElem?_erase,ne] using h

theorem peerGet_keyView (pid : PeerId) : SameView keyView (peerGet pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  obtain ⟨d,p,hd,hp,_,hv⟩ :=
    (hoare_iff_run_ambient _ _ _).mp (PeerBorrow.strict_acquire_spec pid (wgStoreView w))
      w ambient () v ambient' rfl hr
  have hw : w.dev = some d := hd
  have he := congrArg WGStoreView.dev hv
  change v.dev = some _ at he
  unfold keyView keyWords currentCells
  rw [he,hw]
  simp only [Option.map_some,Option.bind_some]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext q
  by_cases eq : pid = q <;> simp_all [Std.TreeMap.getElem?_insert,currentCell]

theorem peerPut_keyEffect (pid : Option PeerId) : KeyEffects allowed (peerPut pid) := by
  apply (KeyEffects.iff_run_ambient _ _).mpr
  intro w ambient x v ambient' hr
  have hl (a : IndexM Unit) : (liftM a : WG.M Unit) = liftIndex a := rfl
  cases pid with
  | none =>
    simp [peerPut,branch,CounterWindow.branch_run,StateT.run_bind,
      StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind,
      CounterWindow.except_pure] at hr
    rcases hr with ⟨rfl,rfl⟩
    exact KeyEffect.refl _ _
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerPut,branch,CounterWindow.branch_run,requireNotPending,
        getPeer,getDev,hd,invariant,AmbientM.invariant,StateT.run_bind,
        StateT.run_monadLift,CounterWindow.except_ok_bind] at hr
      change Except.error _ = Except.ok ((x,v),ambient') at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerPut,branch,CounterWindow.branch_run,requireNotPending,
          getPeer,getDev,hd,hp,invariant,AmbientM.invariant,StateT.run_bind,
          StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind] at hr
        change Except.error _ = Except.ok ((x,v),ambient') at hr
        cases hr
      | some p =>
        by_cases zero : p.refcount = 0
        · simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
            CounterWindow.branchCmp_run,hd,hp,zero,StateT.run_bind,StateT.run_pure,
            StateT.run_monadLift,CounterWindow.except_ok_bind,CounterWindow.except_pure,
            unsupported,AmbientM.unsupported] at hr
          change Except.error _ = Except.ok ((x,v),ambient') at hr
          cases hr
        · have positive : 0 < p.refcount := Nat.pos_of_ne_zero zero
          by_cases final : p.refcount = 1
          all_goals
            simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
              refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,
              hl,liftIndex_run,retirePeerUnits,modifyAmbient,
              CounterWindow.branch_run,CounterWindow.branchCmp_run,hd,hp,positive,zero,final,
              StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
              CounterWindow.except_ok_bind,CounterWindow.except_pure,
              invariant,AmbientM.invariant,unsupported,AmbientM.unsupported] at hr
          all_goals repeat' first | split at hr | contradiction
          all_goals rcases hr with ⟨rfl,rfl⟩
          all_goals refine ⟨?_,?_,?_⟩
          all_goals first
            | solve | simp [keyView,hd]
            | solve | intro k q h; simpa [keyView,keyWords,hd] using h
            | (intro q stamp current h
               refine ⟨current,?_,Or.inl rfl⟩
               by_cases he : pid = q <;>
                 simp_all [keyView,currentCells,currentCell,
                   Std.TreeMap.getElem?_erase,Std.TreeMap.getElem?_insert])

theorem getKey_effect (allowed) (initial : WGWorld) (kid : KeypairId) :
    ⦃fun w => ⌜KeyEffect allowed initial w⌝⦄ getKeypair kid
    ⦃⇓? k w => ⌜KeyEffect allowed initial w ∧ Affiliation.keyAt w kid=some (Affiliation.keyCell k)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient key v ambient' hi hr
  obtain ⟨rfl,_,d,hd,hk⟩ := KeyTimes.getKeypair_return kid w v key ambient ambient' hr
  exact ⟨hi,by simp [Affiliation.keyAt,hd,hk]⟩

theorem setKey_effect (allowed) (initial : WGWorld) (kid : KeypairId) (k : Keypair) :
    ⦃fun w => ⌜KeyEffect allowed initial w ∧ Affiliation.keyAt w kid=some (Affiliation.keyCell k)⌝⦄ setKeypair kid k
    ⦃⇓? _ w => ⌜KeyEffect allowed initial w⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  have he := (hoare_iff_run_ambient _ _ _).mp
    (Affiliation.setKeypair_spec (fun t => t=Affiliation.view w) kid k)
      w ambient x v ambient' ⟨rfl,hi.2⟩ hr
  exact hi.1.trans (keyEffect_of_view (keyView_affiliation he))

theorem eraseKey_effect (kid : KeypairId) :
    KeyEffects allowed (modifyDev fun d => {d with keypairs:=d.keypairs.erase kid}) := by
  apply (KeyEffects.iff_run_ambient _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  constructor
  · simp [keyView,Option.map_map,Function.comp_def]
  · intro k p h
    cases hd : w.dev with
    | none => simp [keyView,keyWords,hd] at h
    | some d =>
      by_cases he : kid=k
      · simp [keyView,keyWords,hd,he] at h
      · simpa [keyView,keyWords,hd,Std.TreeMap.getElem?_erase,he] using h
  · intro p s c h
    exact ⟨c,by simpa [keyView,currentCells,Option.bind_map,Function.comp_def] using h,Or.inl rfl⟩

theorem keypairPut_keyEffect (kp : Option KeypairId) (now : Bool) : KeyEffects allowed (keypairPut kp now) := by
  apply (KeyEffects.iff_run_ambient _ _).mpr
  intro w ambient x v ambient' hr
  let P := fun s => KeyRelation allowed (keyView w) (stateKeyView s)
  have closed : ∀s kid,P (some s) → P (some (s.eraseKey kid)) := by
    intro s kid h
    refine ⟨h.epoch,?_,h.currents⟩
    intro k pid hk
    by_cases he : k=kid
    · simp [stateKeyView,Affiliation.State.eraseKey,he] at hk
    · exact h.words k pid (by simpa [stateKeyView,Affiliation.State.eraseKey,he] using hk)
  have hi : P (Affiliation.view w) := by simpa [P,←keyView_factor] using KeyEffect.refl allowed w
  have result := (hoare_iff_run_ambient _ _ _).mp (Affiliation.keypairPut_affiliation P closed kp now) w ambient x v ambient' hi hr
  simpa [P,←keyView_factor] using result

theorem control_keyView (he : controlView v=controlView w) : keyView v=keyView w := by
  refine Prod.ext (congrArg (fun s => s.1.1.1) he) (Prod.ext (congrArg (fun s => s.2.2) he) ?_)
  funext pid
  have hp := congrFun (congrArg (fun s => s.1.1.2) he) pid
  have hc := congrFun (congrArg (fun s => s.2.1) he) pid
  simp only [controlView,protectView,peerView,currentKey] at hp hc
  change (v.dev.bind fun d => d.peers[pid]?).map currentCell = (w.dev.bind fun d => d.peers[pid]?).map currentCell
  cases hv : (v.dev.bind fun d => d.peers[pid]?) <;>
    cases hw : (w.dev.bind fun d => d.peers[pid]?) <;> simp_all [currentCell]

theorem control_keyEffects {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => controlView (project w)) a) :
    ProjectedKeyEffects project allowed a := by
  apply keyEffects_view
  intro initial
  apply hoare_consequence
    (ha.wp (fun obs => ∃ w, obs = controlView w ∧ keyView w = initial))
  · intro w hi; exact ⟨project w,rfl,hi⟩
  · intro x w hi
    obtain ⟨old,he,hi⟩ := hi
    exact (control_keyView he).trans hi

theorem modifyPeer_keyView (pid : PeerId) (f : Peer → Peer)
    (hf : ∀p,currentCell (f p)=currentCell p) :
    SameView keyView ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by
  change SameView keyView (do let p ← getPeer pid; setPeer pid (f p))
  intro initial
  apply hoare_bind _ _ (getPeer_key_spec (fun t => t = initial) pid)
  intro p
  apply hoare_consequence (setPeer_key_spec (fun t => t = initial) pid (f p))
  · intro w hi; exact ⟨hi.1,by simpa [hf] using hi.2⟩
  · exact fun _ _ hi => hi

theorem promotion_effect (pid kid : Nat) :
    KeyEffects (ReceivedPromotion pid kid)
      ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairCurrent:=some kid,keypairNext:=none})) := by
  apply (KeyEffects.iff_run_ambient _ _).mpr
  intro w ambient x v ambient' hr
  change ((do let p ← getPeer pid; setPeer pid {p with keypairCurrent:=some kid,keypairNext:=none}).run w).run ambient = .ok ((x,v),ambient') at hr
  obtain ⟨p,a,midway,hget,hset⟩ := bind_ok_native hr
  obtain ⟨rfl,_,d,hd,hp⟩ := getPeer_normal pid w a p ambient midway hget
  cases hset
  refine ⟨by simp [keyView,hd],?_,?_⟩
  · intro k q h; simpa [keyView,keyWords,hd] using h
  · intro q stamp current h
    by_cases hq : pid = q
    · subst q
      simp [keyView,currentCells,currentCell,hd] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨p.keypairCurrent,by simp [keyView,currentCells,currentCell,hd,hp],
        Or.inr ⟨kid,rfl,rfl,rfl⟩⟩
    · exact ⟨current,by simpa [keyView,currentCells,hd,Std.TreeMap.getElem?_insert,hq] using h,Or.inl rfl⟩

theorem receivedWithKeypair_keyEffect (pid kid : Nat) :
    KeyEffects (ReceivedPromotion pid kid) (receivedWithKeypair pid kid) := by
  apply keyEffects_of_wp
  intro initial
  let P := KeyEffect (ReceivedPromotion pid kid) initial
  have getter (target : PeerId) : Preserves P (getPeer target) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' hi hr
    obtain ⟨rfl,_,_,_,_⟩ := getPeer_normal target w v p ambient ambient' hr
    exact hi
  have hk := fun old => KeyEffects.wp (keypairPut_keyEffect (allowed:=ReceivedPromotion pid kid) old true) initial
  have hm := (modifyPeer_keyView pid (fun p => {p with keypairPrevious:=p.keypairCurrent})
    (fun _ => rfl)).wp (KeyRelation (ReceivedPromotion pid kid) (keyView initial))
  have hs := KeyEffects.wp (promotion_effect pid kid) initial
  change Preserves P (receivedWithKeypair pid kid)
  unfold receivedWithKeypair
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact getter _)
    | (index_material_head keypairPut; exact hk _)
    | (index_material_head modifyPeer; first | exact hm | exact hs)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

/-- Resident RX cells require only nullable ownership of their actual key. -/
def RxCompatible (w : WGWorld) : Prop := ∀(d : Device) (id : SkbId) (pkt : RxPacket),
  w.dev=some d → d.rxSkbs[id]?=some pkt → KeyCompatible pkt.peer pkt.keypair w
def CurrentsCompatible (w : WGWorld) : Prop := ∀pid,CurrentCompatible pid w
def KeysCompatible (w : WGWorld) : Prop := RxCompatible w ∧ CurrentsCompatible w

theorem KeyEffect.compatible (h : KeyEffect allowed w v) (hc : KeyCompatible pid kid w) : KeyCompatible pid kid v := by
  rw [compatible_words] at hc ⊢
  intro word hw
  cases word with
  | none => exact Or.inl rfl
  | some owner => exact hc _ (h.words kid owner hw)

theorem KeyEffect.currentsCompatible (h : KeyEffect allowed w v) (hc : CurrentsCompatible w)
    (ha : ∀pid kid,allowed pid kid → KeyCompatible pid kid w) : CurrentsCompatible v := by
  intro pid d p kid hd hp hk
  have cell : currentCells v pid=some (p.internalId,some kid) := by simp [currentCells,currentCell,hd,hp,hk]
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
  have old : (w.dev.bind fun d => d.rxSkbs[id]?)=some pkt := by simpa [rxView,hd,hp] using slots.symm
  obtain ⟨od,hod,hp⟩ := Option.bind_eq_some_iff.mp old
  exact h.compatible (hc od id pkt hod hp)

theorem cpu_keyView (pid : PeerId) : SameView keyView (cpumaskChooseOnline pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  unfold cpumaskChooseOnline at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,a,readAmbient,hg,hr⟩ := hr
  obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal pid w a p ambient readAmbient hg
  by_cases invalid : p.serialWorkCpu.getD 1 ≥ 1
  all_goals
    simp [Nat.mod_one,invalid,getPeer,getDev,setPeer,modifyDev,branch,
      StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
      CounterWindow.except_ok_bind,CounterWindow.except_pure,hd,hp] at hr
  all_goals rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩
  all_goals unfold keyView keyWords currentCells
  all_goals simp [hd,Std.TreeMap.getElem?_insert,funext_iff]
  all_goals intro q; by_cases he : pid = q <;> simp_all [currentCell]

theorem enqueue_keyView (pid : PeerId) (item : List SkbId) : SameView keyView (enqueuePerDeviceAndPeer pid item) := by
  intro initial
  let P : WGWorld → Prop := fun w => keyView w = initial
  have tail : Preserves P (enqueueTailItem item) := by
    have hg := (keyView_kernel (project := id) getDev_sameWGStore).wp (fun t => t = initial)
    have hc := fun last => (keyView_kernel (project := id) (cpumaskNextOnlineFrom_sameStore last)).wp (fun t => t = initial)
    have hcpu := fun cpu => (modifyDev_keyView (fun d => {d with encryptLastCpu := cpu})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = initial)
    have hring := (modifyDev_keyView (fun d => {d with encryptQueue := d.encryptQueue.produce item})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = initial)
    unfold enqueueTailItem
    apply preserves_bind hg
    intro d
    apply preserves_bind (hc d.encryptLastCpu)
    intro cpu
    apply preserves_bind (hcpu cpu)
    intro _
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .enqueueRingFull d.encryptQueue.full) P)
    intro full
    cases full with
    | true =>
      simp only [ite_true]
      exact preserves_pure _
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      apply preserves_bind (hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker) P)
      intro _
      apply preserves_bind hring
      intro _
      exact preserves_pure _
  rw [enqueue_factor]
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  cases head : item.head? with
  | none =>
    simp only [head,invariant,AmbientM.invariant] at hr
    cases hr
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨u,a,aa,hset,p,b,ab,hget,full,c,ac,hbranch,hr⟩ := hr
    have ha := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftSkb (SkbStore.setTx first (fun p => {p with state := .uncrypted})) P (by
        intro g d s h hd
        unfold P keyView keyWords currentCells at h ⊢
        simpa only [hd,Option.map_some,Option.bind_some] using h))
      w ambient u a aa hi hset
    have hb := (hoare_iff_run_ambient _ _ _).mp (getPeer_key_spec (fun t => t = initial) pid)
      a aa p b ab ha hget
    have hc := ((hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (fun g => keyView g = initial ∧ currentCells g pid = some (currentCell p))
        .enqueuePeerQueueFull (decide (p.txQueue.count ≥ MAX_QUEUED_PACKETS)))
      b ab full c ac hb hbranch).2
    cases full with
    | true =>
      simp only [ite_true] at hr
      cases hr
      exact hc.1
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
      obtain ⟨u,e,ae,hinstall,htail⟩ := hr
      have he := (hoare_iff_run_ambient _ _ _).mp
        (setPeer_key_spec (fun t => t = initial) pid {p with txQueue := p.txQueue.enqueue item})
        c ac u e ae hc hinstall
      exact (hoare_iff_run_ambient _ _ _).mp tail e ae result v ambient' he htail

theorem publication_keyEffect (item : List SkbId) (state : PacketState) :
    KeyEffects allowed (enqueuePerPeerTx item state) := by
  apply keyEffects_of_wp; intro initial
  let P := KeyEffect allowed initial
  have getter (pid : PeerId) : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_effect allowed initial pid) (fun _ h => h) (fun _ _ h => h.1)
  have skbs {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb
    intro w d s hi hd
    unfold P KeyEffect keyView keyWords currentCells at hi ⊢
    simpa only [id_eq,hd,Option.map_some,Option.bind_some] using hi
  have hp := fun pid => KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed) (peerGet_keyView pid)) initial
  have hf := fun pid => KeyEffects.wp (peerPut_keyEffect (allowed := allowed) pid) initial
  have hc := fun pid => KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed) (cpu_keyView pid)) initial
  have owner := fun o => indexOwner_peerDeref_preserves o P
  have dev := (keyView_kernel (project := id) getDev_sameWGStore).wp (KeyRelation allowed (keyView initial))
  have hm := fun pid => KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed) (modifyDev_keyView
    (fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))) initial
  change Preserves P _
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [getTxSkb,setTxSkb,invariant,peekQueuedUnit,recordQueued]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact getter _)
    | (index_material_head liftSkb; exact skbs _)
    | (index_material_head peerGet; exact hp _)
    | (index_material_head peerPut; exact hf _)
    | (index_material_head cpumaskChooseOnline; exact hc _)
    | (index_material_head IndexOwner.peerDeref; exact owner _)
    | (index_material_head getDev; exact dev)
    | (index_material_head modifyDev; exact hm _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem createData_keyEffect (pid : PeerId) (item : List SkbId) : KeyEffects allowed (createData pid item) := by
  apply keyEffects_of_wp; intro initial
  let P := KeyEffect allowed initial
  have hd := KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed) (enqueue_keyView pid item)) initial
  have hp := KeyEffects.wp (publication_keyEffect (allowed := allowed) item .dead) initial
  have hk := fun id => KeyEffects.wp (keypairPut_keyEffect (allowed := allowed) id false) initial
  have hr := KeyEffects.wp (peerPut_keyEffect (allowed := allowed) (some pid)) initial
  have getter : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_effect allowed initial pid) (fun _ h => h) (fun _ _ h => h.1)
  have skbs {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by
    apply hoare_liftSkb
    intro w d s hi hd
    unfold P KeyEffect keyView keyWords currentCells at hi ⊢
    simpa only [id_eq,hd,Option.map_some,Option.bind_some] using hi
  change Preserves P _
  unfold createData
  simp (config := {zeta := false}) only [getTxSkb,freeTxSkb,branch,invariant]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head enqueuePerDeviceAndPeer; exact hd)
    | (index_material_head enqueuePerPeerTx; exact hp)
    | (index_material_head keypairPut; exact hk _)
    | (index_material_head peerPut; exact hr)
    | (index_material_head getPeer; exact getter)
    | (index_material_head liftSkb; exact skbs _)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem queued_keyEffect (pid : PeerId) (retry : Bool) : KeyEffects allowed (sendQueuedHandshakeInitiation pid retry) := by
  apply keyEffects_of_wp; intro initial
  let P := KeyEffect allowed initial
  have getter : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_effect allowed initial pid) (fun _ h => h) (fun _ _ h => h.1)
  have setter := fun f hf => KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed)
    (modifyPeer_keyView pid f hf)) initial
  have hp := KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed) (peerGet_keyView pid)) initial
  have hf := KeyEffects.wp (peerPut_keyEffect (allowed := allowed) (some pid)) initial
  have ht := fun date => (branchExpired_sameWGWorld .queuedNotExpired date REKEY_TIMEOUT (!·)).wp P
  have hm := KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed) (modifyDev_keyView
    (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))) initial
  rw [← queuedSource_eq]
  change Preserves P _
  unfold queuedSource handshakeBorrow handshakeQueueTail
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact getter)
    | (index_material_head modifyPeer; exact setter _ (fun _ => rfl))
    | (index_material_head peerGet; exact hp)
    | (index_material_head peerPut; exact hf)
    | (index_material_head branchExpired; exact ht _)
    | (index_material_head modifyDev; exact hm)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem stagedOutNokey_keyEffect (pid : PeerId) (packets : List WG.Packet) (kp : Option KeypairId) (invalid : Bool) :
    KeyEffects allowed (Lifetimes.stagedOutNokey pid packets kp invalid) := by
  apply keyEffects_of_wp; intro initial
  let P := KeyEffect allowed initial
  let tail : WG.M Unit := do
    keypairPut kp false
    for _ in packets do _ ← branch .stagedOrphanWalk true
    _ ← branch .stagedOrphanWalk false
    let p ← getPeer pid
    setPeer pid {p with staged := packets ++ p.staged}
    sendQueuedHandshakeInitiation pid false
  have ht : Preserves P tail := by
    unfold tail
    apply preserves_bind (KeyEffects.wp (keypairPut_keyEffect (allowed := allowed) kp false) initial)
    intro _
    apply preserves_bind
    · apply list_view_spec id P
      intro pkt acc
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .stagedOrphanWalk true) P)
      intro _
      exact preserves_pure _
    · intro _
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .stagedOrphanWalk false) P)
      intro _
      apply hoare_bind _ _ (getPeer_effect allowed initial pid)
      intro p
      apply hoare_bind _ _ (hoare_consequence
        (setPeer_effect allowed initial pid {p with staged := packets ++ p.staged})
        (fun _ h => ⟨h.1,by simpa only [currentCell] using h.2⟩) (fun _ _ h => h))
      intro _
      exact KeyEffects.wp (queued_keyEffect (allowed := allowed) pid false) initial
  change Preserves P _
  unfold Lifetimes.stagedOutNokey
  simp only [getPeer_twice]
  cases invalid with
  | false => exact ht
  | true =>
    cases kp with
    | none =>
      apply preserves_bind (hoare_liftAmbient (AmbientM.invariant "unreachable") P)
      intro _
      exact ht
    | some target =>
      apply hoare_bind _ _ (getKey_effect allowed initial target)
      intro k
      apply hoare_bind _ _ (hoare_consequence
        (setKey_effect allowed initial target {k with sending := {k.sending with isValid := false}})
        (fun _ h => ⟨h.1,by simpa only [Affiliation.keyCell] using h.2⟩) (fun _ _ h => h))
      intro _
      exact ht

theorem stagedSubmit_keyEffect (pid kid : Nat) (packets : List DataPacket) : KeyEffects allowed (stagedSubmit pid kid packets) := by
  apply keyEffects_of_wp; intro initial
  let P := KeyEffect allowed initial
  have alloc : Preserves P (packets.mapM newTxSkb) := by
    apply mapM_view_spec id P
    intro packet
    unfold newTxSkb
    apply hoare_liftSkb
    intro w d s hi hd
    unfold P KeyEffect keyView keyWords currentCells at hi ⊢
    simpa only [id_eq,hd,Option.map_some,Option.bind_some] using hi
  unfold stagedSubmit Affiliation.sendAcquire
  simp only [bind_assoc]
  apply preserves_bind (indexOwner_peerDeref_preserves (.keypair kid) P)
  intro pid'
  apply preserves_bind (KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed) (peerGet_keyView pid')) initial)
  intro _
  apply preserves_bind alloc
  intro item
  exact KeyEffects.wp (createData_keyEffect (allowed := allowed) pid item) initial

theorem stagedKeySource_keyEffect (pid kid : Nat) (packets : List WG.Packet) :
    KeyEffects allowed (stagedKeySource pid kid packets) := by
  apply keyEffects_of_wp; intro initial
  let P := KeyEffect allowed initial
  let nonceStep : WG.M Nat := do
    let k ← getKeypair kid
    setKeypair kid {k with sendingCounter := k.sendingCounter + 1}
    pure k.sendingCounter
  have nonce_spec : Preserves P nonceStep := by
    unfold nonceStep
    apply hoare_bind _ _ (getKey_effect allowed initial kid)
    intro k
    apply hoare_bind _ _ (hoare_consequence
      (setKey_effect allowed initial kid {k with sendingCounter := k.sendingCounter + 1})
      (fun _ h => ⟨h.1,by simpa only [Affiliation.keyCell] using h.2⟩) (fun _ _ h => h))
    intro _
    exact preserves_pure _
  have getter := hoare_consequence (getKey_effect allowed initial kid)
    (fun _ h => h) (fun _ _ h => h.1)
  have expired := fun date =>
    (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp P
  have ecn := fun pkt => (Lifetimes.ipTunnelEcnEncap_sameWGWorld pkt).wp P
  have out := fun invalid => KeyEffects.wp (stagedOutNokey_keyEffect (allowed := allowed) pid packets (some kid) invalid) initial
  have submit := fun ps => KeyEffects.wp (stagedSubmit_keyEffect (allowed := allowed) pid kid ps) initial
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
  change Preserves P _
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | unfold Preserves
    | exact nonce_spec
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter)
    | (index_material_head branchExpired; exact expired _)
    | (index_material_head ipTunnelEcnEncap; exact ecn _)
    | (index_material_head Lifetimes.stagedOutNokey; exact out _)
    | (index_material_head stagedSubmit; exact submit _)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem staged_send_keyEffect (pid : PeerId) : KeyEffects allowed (sendStagedPackets pid) := by
  apply (KeyEffects.iff_run_ambient _ _).mpr
  intro w ambient x v ambient' hr
  cases x
  rw [← stagedFullSource_eq] at hr
  simp only [stagedFullSource,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,a,aa,hget,empty,b,ab,hbranch,hr⟩ := hr
  have ha := (hoare_iff_run_ambient _ _ _).mp (getPeer_effect allowed w pid)
    w ambient p a aa (KeyEffect.refl _ _) hget
  have hb := ((hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (fun g => KeyEffect allowed w g ∧ currentCells g pid = some (currentCell p))
      .stagedEmpty p.staged.isEmpty)
    a aa empty b ab ha hbranch).2
  cases empty with
  | true =>
    simp only [ite_true] at hr
    cases hr
    exact hb.1
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at hr
    obtain ⟨u,c,ac,hset,kp,d,ad,hkey,absent,e,ae,habsent,hr⟩ := hr
    have hc := (hoare_iff_run_ambient _ _ _).mp
      (setPeer_effect allowed w pid {p with staged := []}) b ab u c ac hb hset
    have hd := hc.trans (keyEffect_of_view ((ProjectedAction.iff_run_ambient _ _ _).mp
      (keypairGet_keyView p.keypairCurrent) c ac kp d ad hkey))
    have he := ((hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (KeyEffect allowed w) .stagedNoKeypair kp.isNone)
      d ad absent e ae hd habsent).2
    cases absent with
    | true =>
      simp only [ite_true] at hr
      exact (hoare_iff_run_ambient _ _ _).mp
        (KeyEffects.wp (stagedOutNokey_keyEffect (allowed := allowed) pid p.staged kp false) w)
        e ae () v ambient' he hr
    | false =>
      simp only [Bool.false_eq_true,ite_false] at hr
      cases kp with
      | none =>
        simp only [invariant,AmbientM.invariant] at hr
        cases hr
      | some kid =>
        exact (hoare_iff_run_ambient _ _ _).mp
          (KeyEffects.wp (stagedKeySource_keyEffect (allowed := allowed) pid kid p.staged) w)
          e ae () v ambient' he hr

theorem updateRxStats_keyView (pid : PeerId) (len : Nat) : SameView keyView (updateRxStats pid len) := by
  unfold updateRxStats
  apply SameView.bind (modifyDev_keyView (fun d => {d with rxPackets := d.rxPackets + 1,rxBytes := d.rxBytes + len})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  intro _
  exact modifyPeer_keyView pid (fun p => {p with rxBytes := p.rxBytes + len}) (fun _ => rfl)

theorem dishonest_keyView (why : Dishonest) : SameView keyView (dishonest why) :=
  modifyDev_keyView _ (fun _ => by cases why <;> rfl) (fun _ => by cases why <;> rfl) (fun _ => by cases why <;> rfl)

theorem keepKeyFreshRx_keyEffect (pid : PeerId) : KeyEffects allowed (keepKeyFreshRx pid) := by
  apply keyEffects_of_wp; intro initial
  let P := KeyEffect allowed initial
  have getter : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_effect allowed initial pid) (fun _ h => h) (fun _ _ h => h.1)
  have keyGetter (kid : KeypairId) : Preserves P (getKeypair kid) :=
    hoare_consequence (getKey_effect allowed initial kid) (fun _ h => h) (fun _ _ h => h.1)
  have setter := KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed)
    (modifyPeer_keyView pid (fun p => {p with sentLastminuteHandshake := true}) (fun _ => rfl))) initial
  have expired := fun date delay => (branchExpired_sameWGWorld .rxFreshExpired date delay).wp P
  have queued := KeyEffects.wp (queued_keyEffect (allowed := allowed) pid false) initial
  have source : keepKeyFreshRx pid = (do
      if ← branch .rxFreshSentLastminute (← getPeer pid).sentLastminuteHandshake then return
      let current := (← getPeer pid).keypairCurrent
      let send ← WG.andM (branch .rxFreshKeypair current.isSome) do
        let some id := current | invariant "unreachable"
        let k ← getKeypair id
        WG.andM (branch .rxFreshValid k.sending.isValid) do
          WG.andM (branch .rxFreshInitiator k.iAmTheInitiator) do
            branchExpired .rxFreshExpired k.sending.birthdate (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)
      if ← branch .rxFreshSend send then
        ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
          (fun p => {p with sentLastminuteHandshake := true}))
        sendQueuedHandshakeInitiation pid false) := by
    simp only [keepKeyFreshRx,modifyPeer_source,bind_assoc] <;> rfl
  rw [source]
  change Preserves P _
  simp (config := {zeta := false}) only [WG.andM,branch,invariant]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact getter)
    | (index_material_head getKeypair; exact keyGetter _)
    | (index_material_head modifyPeer; exact setter)
    | (index_material_head branchExpired; exact expired _ _)
    | (index_material_head sendQueuedHandshakeInitiation; exact queued)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem promoteAndSend_keyEffect (pid kid : Nat) :
    KeyEffects (ReceivedPromotion pid kid) (promoteAndSend pid kid) := by
  apply keyEffects_of_wp; intro initial
  let P := KeyEffect (ReceivedPromotion pid kid) initial
  have hp := KeyEffects.wp (receivedWithKeypair_keyEffect pid kid) initial
  have ht := KeyEffects.wp (control_keyEffects (allowed := ReceivedPromotion pid kid)
    (timersHandshakeComplete_control pid .walltimeLastHandshakeData)) initial
  have hs := KeyEffects.wp (staged_send_keyEffect (allowed := ReceivedPromotion pid kid) pid) initial
  change Preserves P _
  unfold promoteAndSend
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head receivedWithKeypair; exact hp)
    | (index_material_head timersHandshakeComplete; exact ht)
    | (index_material_head sendStagedPackets; exact hs)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem prepareRest_keyEffect (pid : PeerId) (pkt : RxPacket) : KeyEffects allowed (prepareRest pid pkt) := by
  apply keyEffects_of_wp; intro initial
  let P := KeyEffect allowed initial
  have hf := KeyEffects.wp (keepKeyFreshRx_keyEffect (allowed := allowed) pid) initial
  have ha := KeyEffects.wp (control_keyEffects (allowed := allowed) (delTimer_control pid .newHandshake)) initial
  have ht := KeyEffects.wp (control_keyEffects (allowed := allowed) (timersTraversal_control pid)) initial
  have hd := KeyEffects.wp (control_keyEffects (allowed := allowed) (timersDataReceived_control pid)) initial
  have hs := fun len => KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed) (updateRxStats_keyView pid len)) initial
  have he := fun why => KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed) (dishonest_keyView why)) initial
  have hc := fun proto outer bytes => KeyEffects.wp (keyEffects_view (project := id) (allowed := allowed)
    (keyView_kernel (project := id) (Lifetimes.inetEcnDecapsulate_sameWGStore proto outer bytes))) initial
  change Preserves P _
  unfold prepareRest timersAnyAuthenticatedPacketReceived
  simp (config := {zeta := false}) only [WG.andM,WG.orM,branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head keepKeyFreshRx; exact hf)
    | (index_material_head delTimer; exact ha)
    | (index_material_head timersTraversal; exact ht)
    | (index_material_head timersDataReceived; exact hd)
    | (index_material_head updateRxStats; exact hs _)
    | (index_material_head dishonest; exact he _)
    | (index_material_head inetEcnDecapsulate; exact hc _ _ _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

def keyViewOfBorrow (s : WGStoreView × (PeerId → Option Peer)) : KeyView :=
  (s.1.dev.map (·.ifindex),fun kid => (s.1.dev.bind fun d => d.keypairs[kid]?).map (·.peer),
    fun pid => (s.2 pid).map currentCell)

theorem keyView_borrow_factor (w : WGWorld) : keyView w=keyViewOfBorrow (PeerBorrow.view w) := by
  unfold keyView keyViewOfBorrow keyWords currentCells PeerBorrow.view PeerBorrow.outsidePeers PeerBorrow.resident
  cases hd : w.dev <;> simp [wgStoreView,hd]

theorem lookupRepay_keyView (protocol : Nat) (bytes : List UInt8) : SameView keyView (RxBorrow.source protocol bytes) :=
  (RxBorrow.source_frame protocol bytes).of_factor keyViewOfBorrow keyView keyView_borrow_factor

theorem rxFinish_keyView (pid : PeerId) (ready : Packets.RxReady) : SameView keyView (Packets.rxFinish pid ready) := by
  rw [←rxFinishSource_eq]
  intro s
  let P : WGWorld → Prop := fun w => keyView w = s
  change Preserves P (rxFinishSource pid ready)
  unfold rxFinishSource
  material_lower
  repeat' first
    | unfold Preserves
    | (index_material_head RxBorrow.source; exact (lookupRepay_keyView _ _).wp (fun obs => obs = s))
    | (index_material_head dishonest; exact (dishonest_keyView _).wp (fun obs => obs = s))
    | (index_material_head updateRxStats; exact (updateRxStats_keyView _ _).wp (fun obs => obs = s))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

/-- Unconditional normal source effect: only this actual received key can
become the target's new current key. It says nothing about material identity. -/
theorem consumeDataDone_keyEffect (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    KeyEffects (ReceivedPromotion pid pkt.keypair) (consumeDataDone pid pkt endpoint) := by
  apply keyEffects_of_wp
  intro initial
  rw [Packets.consumeDataDone_factor,rxPrepare_factor]
  let P := KeyEffect (ReceivedPromotion pid pkt.keypair) initial
  change Preserves P _
  simp only [bind_assoc]
  repeat' first
    | unfold Preserves
    | (index_material_head setPeerEndpoint
       exact KeyEffects.wp (control_keyEffects (project := id)
         (allowed := ReceivedPromotion pid pkt.keypair) (setPeerEndpoint_control _ _)) initial)
    | (index_material_head promoteAndSend; exact KeyEffects.wp (promoteAndSend_keyEffect _ _) initial)
    | (index_material_head prepareRest
       exact KeyEffects.wp (prepareRest_keyEffect (allowed := ReceivedPromotion pid pkt.keypair) _ _) initial)
    | (index_material_head Packets.rxFinish
       exact KeyEffects.wp (keyEffects_view (project := id)
         (allowed := ReceivedPromotion pid pkt.keypair) (rxFinish_keyView _ _)) initial)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_intro
    | material_reduce
    | material_match

theorem staged_send_keys (pid : PeerId) (hi : KeysCompatible w)
    (ambient ambient' : Ambient)
    (hr : ((sendStagedPackets pid).run w).run ambient = .ok (((),v),ambient')) : KeysCompatible v := by
  have effect := (KeyEffects.iff_run_ambient _ _).mp
    (staged_send_keyEffect (allowed:=NoPromotion) pid) w ambient () v ambient' hr
  obtain ⟨delta,handoff⟩ := staged_send_handoff pid (hi.2 pid) ambient ambient' hr
  exact ⟨effect.rxCompatible handoff.rx hi.1,
    effect.currentsCompatible hi.2 (fun _ _ h => False.elim h)⟩

theorem consumeDataDone_keys (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (hi : KeysCompatible w) (hc : KeyCompatible pid pkt.keypair w)
    (ambient ambient' : Ambient)
    (hr : ((consumeDataDone pid pkt endpoint).run w).run ambient = .ok ((result,v),ambient')) : KeysCompatible v := by
  have effect := (KeyEffects.iff_run_ambient _ _).mp
    (consumeDataDone_keyEffect pid pkt endpoint) w ambient result v ambient' hr
  obtain ⟨delta,handoff⟩ := consumeDataDone_handoff pid pkt endpoint hc ambient ambient' hr
  refine ⟨effect.rxCompatible handoff.rx hi.1,effect.currentsCompatible hi.2 ?_⟩
  intro q k h
  rcases h with ⟨rfl,rfl⟩
  exact hc

end Leanux.Proofs.WG.Queues.RxCredits
