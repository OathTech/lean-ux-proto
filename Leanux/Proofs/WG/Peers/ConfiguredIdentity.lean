import Leanux.Proofs.WG.Keypairs.MaterialOrigin
import Leanux.Proofs.WG.Peers.Affiliation
import Leanux.Proofs.WG.Peers.CreationAccess
import Leanux.Proofs.Framing.WGAllowedIps
import Leanux.Proofs.Framing.WGKernel
import Leanux.Proofs.Framing.Product
import Leanux.Proofs.WG.AllowedIps.ListsMirror
import Leanux.Proofs.WG.AllowedIps.RemovalSource

/-! Configured peer identity is separate from lifetime safety and key affiliation.
The slot frontier bounds slots and hash-table targets, never the process-global
allocation stamp. Dangling/duplicate table rows and dead residents are allowed.
These are supplied-state contracts; no initialized registry is asserted. -/
namespace Leanux.Proofs.WG.ConfiguredIdentity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Std.Do
set_option pp.structureInstances false

structure Cell where
  stamp : Nat
  static : Key
  word : Option PeerId
  dead : Bool
  deriving DecidableEq

def cell (p : Peer) : Cell := ⟨p.internalId,p.remoteStatic,p.handshakeEntryPeer,p.isDead⟩
structure State where
  epoch : Nat
  frontier : Nat
  rows : List (Key × PeerId)
  peers : PeerId → Option Cell

variable {s : State} {pending : Option PeerId} {pid : PeerId} {p old : Cell} {k : Key}

def state (d : Device) : State := ⟨d.ifindex,d.nextPeer,d.peerHashtable,fun p=>d.peers[p]?.map cell⟩
def view (w : WGWorld) : Option State := w.dev.map state

def Self (word : Option PeerId) (pid : PeerId) : Prop := word=none ∨ word=some pid

/-- A newly allocated live peer is temporarily absent from the table. The
exception is discharged by the actual final insertion, not assumed globally. -/
structure State.InvExcept (s : State) (pending : Option PeerId) : Prop where
  bounded : ∀ pid p,s.peers pid=some p → pid<s.frontier
  targets : ∀ key pid,(key,pid)∈s.rows → pid<s.frontier
  rowsMatch : ∀ key pid p,(key,pid)∈s.rows → s.peers pid=some p → p.static=key
  live : ∀ pid p,s.peers pid=some p → p.dead=false → some pid≠pending → (p.static,pid)∈s.rows
  self : ∀ pid p,s.peers pid=some p → Self p.word pid

abbrev State.Inv (s : State) := s.InvExcept none
def InvExcept (pending : Option PeerId) (w : WGWorld) : Prop := ∀s,view w=some s → s.InvExcept pending
abbrev Inv (w : WGWorld) := InvExcept none w

def State.put (s : State) (pid : PeerId) (p : Option Cell) : State :=
  {s with peers:=fun q=>if pid=q then p else s.peers q}

theorem State.InvExcept.put_same (hi : s.InvExcept pending) (hp : s.peers pid=some old)
    (_stamp : p.stamp=old.stamp) (key : p.static=old.static) (word : Self p.word pid)
    (live : p.dead=false → old.dead=false) : (s.put pid (some p)).InvExcept pending := by
  constructor
  · intro q x hx; by_cases he:pid=q
    · subst q; simp only [State.put,ite_true,Option.some.injEq] at hx; subst x; exact hi.bounded _ _ hp
    · exact hi.bounded _ _ (by simpa [State.put,he] using hx)
  · exact hi.targets
  · intro k q x row hx; by_cases he:pid=q
    · subst q; simp only [State.put,ite_true,Option.some.injEq] at hx; subst x
      exact key.trans (hi.rowsMatch _ _ _ row hp)
    · exact hi.rowsMatch _ _ _ row (by simpa [State.put,he] using hx)
  · intro q x hx alive skip; by_cases he:pid=q
    · subst q; simp only [State.put,ite_true,Option.some.injEq] at hx; subst x
      simpa [State.put,key] using hi.live _ _ hp (live alive) skip
    · exact hi.live _ _ (by simpa [State.put,he] using hx) alive skip
  · intro q x hx; by_cases he:pid=q
    · subst q; simp only [State.put,ite_true,Option.some.injEq] at hx; subst x; exact word
    · exact hi.self _ _ (by simpa [State.put,he] using hx)

theorem State.InvExcept.erase (hi : s.InvExcept pending) (pid : PeerId) :
    (s.put pid none).InvExcept pending := by
  have old : ∀q p,(s.put pid none).peers q=some p → s.peers q=some p := by
    intro q p hp; by_cases he:pid=q <;> simp_all [State.put]
  exact ⟨fun _ _ h=>hi.bounded _ _ (old _ _ h),hi.targets,
    fun _ _ _ h hp=>hi.rowsMatch _ _ _ h (old _ _ hp),
    fun _ _ hp hdead skip=>hi.live _ _ (old _ _ hp) hdead skip,
    fun _ _ hp=>hi.self _ _ (old _ _ hp)⟩

def State.allocate (s : State) (key : Key) (stamp : Nat) : State :=
  { s with
    frontier := s.frontier+1
    peers :=fun q=>if s.frontier=q then some ⟨stamp,key,none,false⟩ else s.peers q}

theorem State.Inv.allocate (hi : s.Inv) (key : Key) (stamp : Nat) :
    (s.allocate key stamp).InvExcept (some s.frontier) := by
  constructor
  · intro q p hp; by_cases he:s.frontier=q
    · subst q; exact Nat.lt_succ_self _
    · have := hi.bounded _ _ (by simpa [State.allocate,he] using hp); exact Nat.lt_succ_of_lt this
  · intro k q row; exact Nat.lt_succ_of_lt (hi.targets _ _ row)
  · intro k q p row hp
    have bound := hi.targets _ _ row
    have ne : s.frontier≠q := Nat.ne_of_gt bound
    exact hi.rowsMatch _ _ _ row (by simpa [State.allocate,ne] using hp)
  · intro q p hp alive skip
    have ne : s.frontier≠q := by intro he; subst q; exact skip rfl
    exact hi.live _ _ (by simpa [State.allocate,ne] using hp) alive (by simp)
  · intro q p hp; by_cases he:s.frontier=q
    · subst q; simp only [State.allocate,ite_true,Option.some.injEq] at hp; subst p; exact Or.inl rfl
    · exact hi.self _ _ (by simpa [State.allocate,he] using hp)

def State.insertRow (s : State) (key : Key) (pid : PeerId) : State :=
  {s with rows:=(key,pid)::s.rows}

theorem State.InvExcept.insertRow (hi : s.InvExcept (some pid))
    (hp : s.peers pid=some p) (hkey : p.static=k) : (s.insertRow k pid).Inv := by
  constructor
  · exact hi.bounded
  · intro key q h; rcases List.mem_cons.mp h with eq|h
    · cases eq; exact hi.bounded _ _ hp
    · exact hi.targets _ _ h
  · intro key q x h hx; rcases List.mem_cons.mp h with eq|h
    · cases eq; have e : x=p := Option.some.inj (hx.symm.trans hp); subst x; exact hkey
    · exact hi.rowsMatch _ _ _ h hx
  · intro q x hx alive _; by_cases he:q=pid
    · subst q; have e : x=p := Option.some.inj (hx.symm.trans hp); subst x
      simp [State.insertRow,hkey]
    · exact List.mem_cons_of_mem _ (hi.live _ _ hx alive (by simpa using he))
  · exact hi.self

def State.kill (s : State) (pid : PeerId) : State :=
  { s with
    rows := s.rows.filter (fun r=>r.2!=pid)
    peers :=fun q=>if pid=q then (s.peers q).map (fun p=>{p with dead:=true}) else s.peers q}

theorem State.Inv.kill (hi : s.Inv) (pid : PeerId) : (s.kill pid).Inv := by
  have old : ∀q p,(s.kill pid).peers q=some p → ∃o,s.peers q=some o ∧ p.static=o.static ∧ p.word=o.word ∧ (p.dead=false → o.dead=false) := by
    intro q p hp; by_cases he:pid=q
    · subst q; simp only [State.kill,ite_true] at hp
      obtain ⟨o,ho,rfl⟩ := Option.map_eq_some_iff.mp hp
      exact ⟨o,ho,rfl,rfl,by simp⟩
    · exact ⟨p,by simpa [State.kill,he] using hp,rfl,rfl,id⟩
  constructor
  · intro q p hp; obtain ⟨o,ho,_⟩:=old _ _ hp; exact hi.bounded _ _ ho
  · intro k q h; exact hi.targets _ _ (List.mem_filter.mp h).1
  · intro k q p h hp; obtain ⟨o,ho,key,_⟩:=old _ _ hp
    exact key.trans (hi.rowsMatch _ _ _ (List.mem_filter.mp h).1 ho)
  · intro q p hp alive _
    obtain ⟨o,ho,key,word,dead⟩:=old _ _ hp
    have ne : q≠pid := by
      intro eq; subst q
      simp only [State.kill,ite_true] at hp
      obtain ⟨o,ho,hp⟩:=Option.map_eq_some_iff.mp hp
      cases hp; contradiction
    exact List.mem_filter.mpr ⟨by simpa [State.put,key] using hi.live _ _ ho (dead alive) (by simp),by simpa using ne⟩
  · intro q p hp; obtain ⟨o,ho,key,word,dead⟩:=old _ _ hp
    simpa [word] using hi.self _ _ ho

theorem state_peer_same (d : Device) (pid : PeerId) (old p : Peer)
    (hp : d.peers[pid]?=some old) (he : cell p=cell old) :
    state {d with peers:=d.peers.insert pid p}=state d := by
  unfold state; congr 1; funext q; by_cases h:pid=q
  · subst q; simp [hp,he]
  · simp [Std.TreeMap.getElem?_insert,h]

theorem kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → World} {a : StateT S m α}
    (ha : SameView (fun s => productStoreView (project s)) a) :
    SameView (fun s => view (project s).wg) a :=
  ha.factor (fun k : ProductStore43 => k.2.2.2.dev.map state)

theorem getPeer_spec (P : Option State→Prop) (pid : PeerId) :
    ⦃fun w=>⌜P (view w)⌝⦄ getPeer pid
    ⦃⇓? p w=>⌜P (view w) ∧ (view w).bind (fun s=>s.peers pid)=some (cell p)⌝⦄ := by

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient value out ambient' hi hr
  cases hd : w.dev with
  | none =>
    simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      simp [getPeer, getDev, hd, hp] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨hi, by simp [view, state, hd, hp]⟩

theorem setPeer_spec (P : Option State→Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w=>⌜P (view w) ∧ (view w).bind (fun s=>s.peers pid)=some (cell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w=>⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  cases hd:w.dev with
  | none=>simp [view,hd] at hi
  | some d=>
    obtain ⟨old,ho,he⟩:=Option.map_eq_some_iff.mp (by simpa [view,state,hd] using hi.2)
    cases hr
    simpa [view,setPeer,modifyDev,hd,state_peer_same d pid old p ho he.symm] using hi.1

theorem peerGetMaybeZero_view (peer : Option PeerId) : SameView view (peerGetMaybeZero peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  have hb := ((hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec peer (wgStoreView w)) w ambient result v ambient' rfl hr).2
  change (wgStoreView v).dev.map state = (wgStoreView w).dev.map state
  cases result with
  | none => exact congrArg (fun k : WGStoreView => k.dev.map state) hb
  | some pid =>
    obtain ⟨d,p,hd,hp,hpos,hv⟩ := hb
    simp only [hv,hd,Option.map_some]
    exact congrArg some (state_peer_same d pid p {p with refcount:=p.refcount+1} hp rfl)

/-- Canonical complete-WG/node masks retain every configured-identity field. -/
theorem sameWG {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => wgStoreView (project s)) a) :
    SameView (fun s => view (project s)) a :=
  ha.factor (fun k : WGStoreView => k.dev.map state)

theorem node {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => nodeView (project s)) a) :
    SameView (fun s => view (project s)) a := by
  apply ha.of_factor (fun k : WGStoreView => k.dev.map state) (fun s => view (project s))
  intro w
  simp [view,nodeView,wgStoreView,nodeDevice,state,Option.map_map,Function.comp_def]
  rfl

theorem modifyDev_spec (P : Option State→Prop) (f : Device→Device)
    (h : ∀d,state (f d)=state d) :
    ⦃fun w=>⌜P (view w)⌝⦄ modifyDev f ⦃⇓? _ w=>⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hp hr; cases hr
  simpa [view,modifyDev,Option.map_map,Function.comp_def,h] using hp

theorem precompute (pid : PeerId) : SameView view (precomputeStaticStatic pid) := by

  apply SameView.of_wp
  intro s
  let P := fun w : WGWorld => view w = s
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Preserves Q (StateT.lift a) := hoare_liftAmbient a Q
  have device : Preserves P getDev := by
    unfold getDev
    apply preserves_bind (hoare_consequence (hoare_get P)
      (fun _ h => h) (fun _ _ h => h.2))
    intro w
    cases w.dev
    · exact ambient (AmbientM.invariant "no WireGuard device in this trace's fixture") P
    · exact preserves_pure _
  have clear : Preserves P (do
      let current ← getPeer pid
      setPeer pid {current with precomputedStaticStatic := List.replicate 32 0}) := by
    apply hoare_bind _ _ (getPeer_spec (fun t => t = s) pid)
    intro current
    exact setPeer_spec (fun t => t = s) pid _
  simp only [precomputeStaticStatic, requireNotPending, pure_bind]
  apply hoare_bind _ _ device
  intro d
  apply hoare_bind _ _ (getPeer_spec (fun t => t = s) pid)
  intro p
  apply hoare_bind _ _ (ambient (AmbientM.branch .precomputeNoIdentity !d.staticIdentity.hasIdentity)
    (fun w => P w ∧ (view w).bind (fun state => state.peers pid) = some (cell p)))
  intro noIdentity
  cases noIdentity with
  | true =>
    exact hoare_consequence clear (fun _ h => h.1) (fun _ _ h => h)
  | false =>
    apply hoare_bind _ _ (setPeer_spec (fun t => t = s) pid _)
    intro _
    apply preserves_bind (ambient (AmbientM.branch .precomputeNullPoint
      !(curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2) P)
    intro zero
    cases zero
    · exact preserves_pure _
    · exact clear

theorem cacheReset (pid : PeerId) : SameView view (dstCacheReset pid) := by

  apply SameView.of_wp
  intro s
  let P := fun w : WGWorld => view w = s
  have ambient {α : Type} (a : AmbientM α) : Preserves P (StateT.lift a) :=
    hoare_liftAmbient a P
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  unfold dstCacheReset
  apply preserves_bind (ambient (get : AmbientM Ambient))
  intro a
  apply preserves_bind read
  intro w
  split
  · exact preserves_pure _
  · apply preserves_bind (ambient (AmbientM.hiddenJiffies .dstCacheResetTs))
    intro ts
    apply hoare_bind _ _ (getPeer_spec (fun t => t = s) pid)
    intro p
    exact setPeer_spec (fun t => t = s) pid _

theorem resetHandshake (pid : PeerId) : SameView view (resetLastSentHandshake pid) := by

  apply SameView.of_wp
  intro s
  unfold resetLastSentHandshake
  apply preserves_bind (hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent)
    (fun w => view w = s))
  intro now
  apply hoare_bind _ _ (getPeer_spec (fun t => t = s) pid)
  intro p
  exact setPeer_spec (fun t => t = s) pid _

def State.setWord (s : State) (pid : PeerId) (word : Option PeerId) : State :=
  {s with peers:=fun q=>if pid=q then (s.peers q).map (fun p=>{p with word}) else s.peers q}

theorem State.InvExcept.setWord (hi : s.InvExcept pending) (pid : PeerId) (word : Option PeerId)
    (hw : Self word pid) : (s.setWord pid word).InvExcept pending := by
  cases hp:s.peers pid with
  | none=>
    have he:s.setWord pid word=s := by
      unfold State.setWord; congr 1; funext q; by_cases h:pid=q <;> simp_all
    simpa [he] using hi
  | some p=>
    have he:s.setWord pid word=s.put pid (some {p with word}) := by
      unfold State.setWord State.put; congr 1; funext q; by_cases h:pid=q <;> simp_all
    rw [he]
    exact hi.put_same hp rfl rfl hw (fun h=>h)

theorem word_effect (pid : PeerId) (word : Option PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((IndexOwner.setPeerWord (.handshake pid) word).run w).run ambient=.ok (((),v),ambient')) :
    view v=(view w).map (fun s=>s.setWord pid word) := by
  cases hd:w.dev with
  | none=>simp [IndexOwner.setPeerWord,getPeer,getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
  | some d=>
    cases hp:d.peers[pid]? with
    | none=>simp [IndexOwner.setPeerWord,getPeer,getDev,hd,hp,invariant,AmbientM.invariant] at hr; cases hr
    | some p=>
      simp [IndexOwner.setPeerWord,getPeer,getDev,hd,hp,setPeer,modifyDev] at hr
      rcases hr with ⟨rfl,rfl⟩
      simp only [view,hd,Option.map_some,state,State.setWord]
      congr 2
      funext q; by_cases h:pid=q
      · subst q; simp [hp,cell]
      · simp [Std.TreeMap.getElem?_insert,h]

theorem handshakeInit_effect (pid : PeerId) (psk : Option Key) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((handshakeInit pid psk).run w).run ambient=.ok (((),v),ambient')) :
    view v=(view w).map (fun (s : State)=>s.setWord pid (some pid)) := by
  have hs : ⦃fun u=>⌜view u=(view w).map (fun (s : State)=>s.setWord pid (some pid))⌝⦄
      (do
        if ←branch .handshakeInitHasPsk psk.isSome then
          let p←getPeer pid
          setPeer pid {p with presharedKey:=psk.getD p.presharedKey}
        precomputeStaticStatic pid)
      ⦃⇓? _ u=>⌜view u=(view w).map (fun (s : State)=>s.setWord pid (some pid))⌝⦄ := by
    have hg:=getPeer_spec (fun t=>t=(view w).map (fun (s : State)=>s.setWord pid (some pid))) pid
    have hs:=setPeer_spec (fun t=>t=(view w).map (fun (s : State)=>s.setWord pid (some pid))) pid
    have hp:=(precompute pid).wp (fun t=>t=(view w).map (fun (s : State)=>s.setWord pid (some pid)))
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .handshakeInitHasPsk psk.isSome)
      (fun u => view u = (view w).map (fun (s : State) => s.setWord pid (some pid))))
    intro keyed
    cases keyed with
    | false => exact hp
    | true =>
      apply hoare_bind _ _ hg
      intro p
      apply hoare_bind _ _ (hs {p with presharedKey := psk.getD p.presharedKey})
      intro _
      exact hp
  unfold handshakeInit at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,a,middle,ha,hr⟩:=hr; cases u
  exact (hoare_iff_run_ambient _ _ _).mp hs a middle () v ambient'
    (word_effect _ _ _ _ ambient middle ha) hr


def Creating (pid : PeerId) (key : Key) (v : Option State) : Prop :=
  (∀s,v=some s → s.InvExcept (some pid)) ∧
  ∃s p,v=some s ∧ s.peers pid=some p ∧ p.static=key

theorem core_state (w : WGWorld) (d : Device) (key : Key) (hd : w.dev=some d) :
    view (Peers.creationCoreWorld w d.nextPeer key)=some ((state d).allocate key (w.peerCounter+1)) := by
  simp only [view,Peers.creationCoreWorld,hd,Option.map_some,state,State.allocate]
  congr 2
  funext q; by_cases h:d.nextPeer=q
  · subst q; simp [cell,Peers.createdPeer]
  · simp [Std.TreeMap.getElem?_insert,h]

theorem core_spec (pid : PeerId) (key : Key) :
    ⦃fun w=>⌜Inv w ∧ ∃s,view w=some s ∧ pid=s.frontier⌝⦄ Peers.peerCreateCore pid key
    ⦃⇓? _ w=>⌜Creating pid key (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  rw [Peers.peerCreateCore_run] at hr
  cases hr
  cases hd:w.dev with
  | none=>
    -- The actual caller has already read a Device; this core contract states it.
    simp [view,hd] at hi
  | some d=>
    have hv : view w=some (state d) := by simp [view,hd]
    obtain ⟨initial,hinit,hid⟩:=hi.2
    have he : initial=state d := Option.some.inj (hinit.symm.trans hv)
    subst initial
    change pid=d.nextPeer at hid
    subst pid
    have effect:=core_state w d key hd
    refine ⟨?_,(state d).allocate key (w.peerCounter+1),⟨w.peerCounter+1,key,none,false⟩,effect,?_,rfl⟩
    · intro st hs; rw [effect] at hs; cases hs; exact State.Inv.allocate (hi.1 _ hv) _ _
    · simp [State.allocate,state]

theorem init_creating (pid : PeerId) (key : Key) (psk : Option Key) :
    ⦃fun w=>⌜Creating pid key (view w)⌝⦄ handshakeInit pid psk
    ⦃⇓? _ w=>⌜Creating pid key (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr; cases x
  obtain ⟨hinv,s,p,hv,hp,hkey⟩:=hi
  have effect:=handshakeInit_effect pid psk w v ambient ambient' hr
  rw [hv,Option.map_some] at effect
  refine ⟨?_,s.setWord pid (some pid),{p with word:=some pid},effect,?_,hkey⟩
  · intro st hs; rw [effect] at hs; cases hs; exact (hinv _ hv).setWord _ _ (Or.inr rfl)
  · simp [State.setWord,hp]

def publishRow (pid : PeerId) (key : Key) : WG.M Unit :=
  modifyDev fun d=>{d with peerList:=d.peerList++[pid],peerHashtable:=(key,pid)::d.peerHashtable,numPeers:=d.numPeers+1}


theorem publishRow_effect (pid : PeerId) (key : Key) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((publishRow pid key).run w).run ambient=.ok (((),v),ambient')) :
    view v=(view w).map (fun s=>s.insertRow key pid) := by
  cases hr
  simp only [view,Option.map_map,Function.comp_def]
  rfl

theorem publishRow_spec (pid : PeerId) (key : Key) :
    ⦃fun w=>⌜Creating pid key (view w)⌝⦄ publishRow pid key
    ⦃⇓? _ w=>⌜Inv w ∧ ∃s p,view w=some s ∧ s.peers pid=some p ∧ p.static=key⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr; cases x
  obtain ⟨hinv,s,p,hv,hp,hkey⟩:=hi
  have effect:=publishRow_effect pid key w v ambient ambient' hr
  rw [hv,Option.map_some] at effect
  refine ⟨?_,s.insertRow key pid,p,effect,hp,hkey⟩
  intro st hs; rw [effect] at hs; cases hs
  exact (hinv _ hv).insertRow hp hkey

theorem peerCreate_spec (key : Key) (psk : Option Key) :
    ⦃fun w=>⌜Inv w⌝⦄ peerCreate key psk
    ⦃⇓? result w=>⌜Inv w ∧ ∀pid,result=.ok pid → ∃s p,view w=some s ∧ s.peers pid=some p ∧ p.static=key⌝⦄ := by

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' initial hr
  let P := fun u : WGWorld => view u = view w
  let Q := fun (result : Except Int PeerId) (u : WGWorld) =>
    Inv u ∧ ∀ pid, result = .ok pid →
      ∃ s p, view u = some s ∧ s.peers pid = some p ∧ p.static = key
  have invariant_of (u : WGWorld) (hu : P u) : Inv u := by
    intro st hs
    exact initial st (hu ▸ hs)
  have getter : Hoare getDev P (fun d u => P u ∧ some (state d) = view w) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u a d out b hu hrun
    cases hd : u.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hrun
      cases hrun
    | some saved =>
      simp [getDev, hd] at hrun
      rcases hrun with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨hu, by simpa only [P, view, hd, Option.map_some] using hu⟩
  have ambient_rule {α : Type} (a : AmbientM α) (R : WGWorld → Prop) :
      Preserves R (StateT.lift a) := hoare_liftAmbient a R
  have failure (d : Device) : Hoare (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId))
      (fun u => P u ∧ some (state d) = view w) Q := by
    apply hoare_consequence (hoare_pure (Except.error (-ENOMEM) : Except Int PeerId) _)
    · intro _ h; exact h
    · intro result u h
      rcases h with ⟨rfl, h⟩
      exact ⟨invariant_of u h.1, by simp⟩
  have proof : Hoare (peerCreate key psk) P Q := by
    rw [← Peers.peerCreateFactored_eq]
    unfold Peers.peerCreateFactored
    apply hoare_bind _ _ getter
    intro d
    apply hoare_bind _ _ (ambient_rule (AmbientM.branchCmp .peerCreateMaxPeers
      (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE)
      (fun u => P u ∧ some (state d) = view w))
    intro maxPeers
    cases maxPeers with
    | true => exact failure d
    | false =>
      apply hoare_bind _ _ (ambient_rule (AmbientM.hiddenAlloc .kmemCacheZallocPeer)
        (fun u => P u ∧ some (state d) = view w))
      intro allocated
      apply hoare_bind _ _ (ambient_rule (AmbientM.branch .peerCreateNoMem !allocated)
        (fun u => P u ∧ some (state d) = view w))
      intro noMem
      cases noMem with
      | true => exact failure d
      | false =>
        apply hoare_bind _ _ (ambient_rule (AmbientM.branch .peerCreateDstCacheFail false)
          (fun u => P u ∧ some (state d) = view w))
        intro cacheFailed
        cases cacheFailed with
        | true => exact failure d
        | false =>
          have core : Hoare (Peers.peerCreateCore d.nextPeer key)
              (fun u => P u ∧ some (state d) = view w)
              (fun _ u => Creating d.nextPeer key (view u)) := by
            apply hoare_consequence (core_spec d.nextPeer key)
            · intro u h
              exact ⟨invariant_of u h.1, state d, h.1.trans h.2.symm, rfl⟩
            · intro _ _ h; exact h
          apply hoare_bind _ _ core
          intro _
          apply hoare_bind _ _ (SameView.wp (cacheReset d.nextPeer) (Creating d.nextPeer key))
          intro _
          apply hoare_bind _ _ (init_creating d.nextPeer key psk)
          intro _
          apply hoare_bind _ _ (SameView.wp (resetHandshake d.nextPeer) (Creating d.nextPeer key))
          intro _
          apply hoare_bind _ _ (publishRow_spec d.nextPeer key)
          intro _
          apply hoare_consequence (hoare_pure (Except.ok d.nextPeer : Except Int PeerId) _)
          · intro _ h; exact h
          · intro result u h
            rcases h with ⟨rfl, hi, hx⟩
            refine ⟨hi, ?_⟩
            intro pid he
            cases he
            exact hx
  exact (hoare_iff_run_ambient _ _ _).mp proof w ambient result v ambient' rfl hr

/-- Successful lookup resolves the actual matching table row and actual
borrowed resident peer. No residency, positive-credit or liveness premise is
substituted for the original acquisition. -/
theorem pubkeyLookup_identity (key : Key) (w v : WGWorld) (pid : PeerId)
    (ambient ambient' : Ambient)
    (hi : Inv w) (hr : ((pubkeyLookup key).run w).run ambient=.ok ((some pid,v),ambient')) :
    view v=view w ∧ ∃d p,w.dev=some d ∧ d.peers[pid]?=some p ∧
      (key,pid)∈d.peerHashtable ∧ p.remoteStatic=key ∧ 0<p.refcount := by
  cases hd:w.dev with
  | none=>simp [pubkeyLookup,getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
  | some d=>
    let found := (d.peerHashtable.find? (fun r=>r.1==key)).map Prod.snd
    let recorded := CounterWindow.record ambient .pubkeyLookupMatch found.isSome
    have run : ((peerGetMaybeZero found).run w).run recorded=.ok ((some pid,v),ambient') := by
      simpa [pubkeyLookup,getDev,hd,branch,CounterWindow.branch_run,found,recorded] using hr
    have facts := (hoare_iff_run_ambient _ _ _).mp
      (PeerBorrow.acquire_spec found (wgStoreView w)) w recorded (some pid) v ambient' rfl run
    have chosen : found=some pid := by rcases facts.1 with h|h; cases h; exact h.symm
    obtain ⟨row,hrow,hpid⟩:=Option.map_eq_some_iff.mp chosen
    have hkey : row.1=key := by simpa using List.find?_some hrow
    have member := List.mem_of_find?_eq_some hrow
    obtain ⟨dev,p,hdev,hp,hpos,hv⟩:=facts.2
    have he : dev=d := Option.some.inj (hdev.symm.trans hd)
    subst dev
    have roweq : row=(key,pid) := Prod.ext hkey hpid
    rw [roweq] at member
    have inv:=hi (state d) (by simp [view,hd])
    have static:=inv.rowsMatch key pid (cell p) member (by simp [state,hp])
    refine ⟨?_,d,p,rfl,hp,member,static,hpos⟩
    exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (peerGetMaybeZero_view found) w recorded (some pid) v ambient' run

theorem index {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s =>
      {wgStoreView (project s) with dev := (project s).dev.map fun (d : Device) =>
        {d with indexTable := []}}) a) :
    SameView (fun s => view (project s)) a :=
  ha.of_factor (fun k : WGStoreView => k.dev.map state) (fun s => view (project s))
    (fun s => by cases h : (project s).dev <;> simp [view,h,state])

theorem getKeypair_view (id : KeypairId) : SameView view (getKeypair id) := by

  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient k out ambient' hr
  cases hd : w.dev with
  | none =>
    simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hk : d.keypairs[id]? with
    | none =>
      simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      cases hr
    | some saved =>
      simp [getKeypair, getDev, hd, hk] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      rfl

theorem setKeypair_view (id : KeypairId) (k : Keypair) : SameView view (setKeypair id k) := by
  apply SameView.of_wp; intro s
  simpa only [setKeypair] using modifyDev_spec (fun v=>v=s)
    (fun d=>{d with keypairs:=d.keypairs.insert id k}) (fun _=>rfl)

theorem handshakeZero_view (pid : PeerId) : SameView view (handshakeZero pid) := by

  apply SameView.of_wp
  intro s
  unfold handshakeZero
  apply hoare_bind _ _ (getPeer_spec (fun t => t = s) pid)
  intro p
  exact setPeer_spec (fun t => t = s) pid _

theorem keypairPut_view (kp : Option KeypairId) (unreference : Bool) : SameView view (keypairPut kp unreference) := by

  apply SameView.of_wp
  intro s
  let P := fun w : WGWorld => view w = s
  have ambient {α : Type} (a : AmbientM α) : Preserves P (StateT.lift a) :=
    hoare_liftAmbient a P
  have dec (old : Nat) : Preserves P (refcountDecAndTest old : WG.M Bool) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a r v b hp hr
    by_cases positive : 0 < old <;> by_cases final : old = 1 <;>
      simp [refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        positive, final, unsupported, AmbientM.unsupported] at hr
    all_goals repeat' first | split at hr | contradiction
    all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact hp
  have remove (id : KeypairId) : Preserves P (do
      _ ← IndexOwner.peerDeref (.keypair id)
      indexRemove (.keypair id)) := by
    apply preserves_bind (indexOwner_peerDeref_preserves (.keypair id) P)
    intro _
    apply hoare_liftIndex
    intro g d table hg hd
    simpa only [P, view, hd, Option.map_some, state] using hg
  have tail (id : KeypairId) (k : Keypair) : Preserves P (do
      setKeypair id {k with refcount := k.refcount - 1}
      if ← branch .keypairKrefPutReleased (← refcountDecAndTest k.refcount) then
        (do
          _ ← IndexOwner.peerDeref (.keypair id)
          indexRemove (.keypair id))
        modifyDev fun d => {d with keypairs := d.keypairs.erase id}) := by
    apply preserves_bind (SameView.wp (setKeypair_view id _) (fun t => t = s))
    intro _
    apply preserves_bind (dec k.refcount)
    intro released
    apply preserves_bind (ambient (AmbientM.branch .keypairKrefPutReleased released))
    intro last
    cases last with
    | false => exact preserves_pure _
    | true =>
      apply preserves_bind (remove id)
      intro _
      exact modifyDev_spec (fun t => t = s) _ (fun _ => rfl)
  have branchValue {α : Type} (decision : Decision) (value : Bool)
      (f : Bool → WG.M α) (hf : Preserves P (f value)) :
      Preserves P ((branch decision value : WG.M Bool) >>= f) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a r v b hp hr
    change ((f value).run w).run _ = .ok ((r, v), b) at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hp hr
  cases kp with
  | none =>
    unfold keypairPut
    apply branchValue
    exact preserves_pure _
  | some id =>
    unfold keypairPut
    apply branchValue
    apply preserves_bind (SameView.wp (getKeypair_view id) (fun t => t = s))
    intro k
    apply preserves_bind (ambient (AmbientM.branch .keypairPutUnreferenceNow unreference))
    intro now
    cases now with
    | false => exact tail id k
    | true => exact preserves_bind (remove id) (fun _ => tail id k)

theorem modifyPeer_view (pid : PeerId) (f : Peer→Peer) (hf : ∀p,cell (f p)=cell p) :
    SameView view ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by

  apply SameView.of_wp
  intro s
  change Hoare (do setPeer pid (f (← getPeer pid))) (fun w => view w = s) (fun _ w => view w = s)
  apply hoare_bind _ _ (getPeer_spec (fun t => t = s) pid)
  intro p
  apply hoare_consequence (setPeer_spec (fun t => t = s) pid (f p))
  · intro w h
    exact ⟨h.1, by simpa only [hf p] using h.2⟩
  · intro _ _ h; exact h

theorem addNewKeypair_view (pid : PeerId) (kp : KeypairId) : SameView view (addNewKeypair pid kp) := by

  apply SameView.of_wp
  intro s
  let P := fun w : WGWorld => view w = s
  have ambient (decision : Decision) (value : Bool) :
      Preserves P (branch decision value : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch decision value) P
  have read : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_spec (fun t => t = s) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  have key (id : KeypairId) := SameView.wp (getKeypair_view id) (fun t => t = s)
  have put (id : Option KeypairId) := SameView.wp (keypairPut_view id true) (fun t => t = s)
  have modify (f : Peer → Peer) (hf : ∀ p, cell (f p) = cell p) :=
    SameView.wp (modifyPeer_view pid f hf) (fun t => t = s)
  unfold addNewKeypair
  apply preserves_bind read
  intro p
  apply preserves_bind (key kp)
  intro k
  apply preserves_bind (ambient .addKeypairInitiator k.iAmTheInitiator)
  intro initiator
  cases initiator with
  | false =>
    apply preserves_bind (modify (fun p => {p with keypairNext := some kp}) (fun _ => rfl))
    intro _
    apply preserves_bind (put p.keypairNext)
    intro _
    apply preserves_bind (modify (fun p => {p with keypairPrevious := none}) (fun _ => rfl))
    intro _
    exact put p.keypairPrevious
  | true =>
    apply preserves_bind (ambient .addKeypairHasNext p.keypairNext.isSome)
    intro hasNext
    cases hasNext with
    | false =>
      apply preserves_bind (modify (fun q => {q with keypairPrevious := p.keypairCurrent}) (fun _ => rfl))
      intro _
      apply preserves_bind (put p.keypairPrevious)
      intro _
      exact modify (fun q => {q with keypairCurrent := some kp}) (fun _ => rfl)
    | true =>
      apply preserves_bind (modify (fun q => {q with keypairNext := none, keypairPrevious := p.keypairNext}) (fun _ => rfl))
      intro _
      apply preserves_bind (put p.keypairCurrent)
      intro _
      apply preserves_bind (put p.keypairPrevious)
      intro _
      exact modify (fun q => {q with keypairCurrent := some kp}) (fun _ => rfl)

/-- Retirement removes a slot, and need not remove its stale hash rows. -/
theorem erase_inv (d : Device) (pid dropped : Nat) (hi : (state d).Inv) :
    (state {d with txDropped:=dropped,peers:=d.peers.erase pid}).Inv := by
  have he : state {d with txDropped:=dropped,peers:=d.peers.erase pid}=(state d).put pid none := by
    unfold state State.put; congr 1; funext q
    by_cases h:pid=q <;> simp [Std.TreeMap.getElem?_erase,h]
  rw [he]; exact hi.erase pid

theorem peerPut_preserves (peer : Option PeerId) :
    ⦃fun w=>⌜Inv w⌝⦄ peerPut peer ⦃⇓? _ w=>⌜Inv w⌝⦄ := by

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result out ambient' hinv hr
  cases peer with
  | none =>
    simp [peerPut, branch, AmbientM.branch] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact hinv
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerPut, requireNotPending, getPeer, getDev, hd, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerPut, requireNotPending, getPeer, getDev, hd, hp, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at hr
        cases hr
      | some p =>
        have initial : (state d).Inv := hinv (state d) (by simp [view, hd])
        have updated : (state {d with peers := d.peers.insert pid {p with refcount := p.refcount - 1}}).Inv := by
          rw [state_peer_same d pid p {p with refcount := p.refcount - 1} hp rfl]
          exact initial
        have erased : (state {d with peers := (d.peers.insert pid {p with refcount := p.refcount - 1}).erase pid}).Inv :=
          erase_inv {d with peers := d.peers.insert pid {p with refcount := p.refcount - 1}} pid d.txDropped updated
        have hl (a : IndexM Unit) : (liftM a : WG.M Unit) = liftIndex a := rfl
        by_cases positive : 0 < p.refcount
        · have nonzero : p.refcount ≠ 0 := by omega
          by_cases final : p.refcount = 1
          all_goals
            simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
              refcountDecAndTest, branch, branchCmp, indexRemove_eq, indexUnhash,
              hl, liftIndex_run, retirePeerUnits, modifyAmbient,
              CounterWindow.branch_run, CounterWindow.branchCmp_run,
              hd, hp, positive, nonzero, final,
              StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              CounterWindow.except_ok_bind, CounterWindow.except_pure,
              invariant, AmbientM.invariant, unsupported, AmbientM.unsupported] at hr
          all_goals repeat' first | split at hr | contradiction
          all_goals rcases hr with ⟨rfl, rfl⟩
          all_goals
            intro st hs
            simp only [view, Option.map_some, Option.some.injEq] at hs
            subst st
            first | simpa only [state, final, Nat.sub_self] using erased | exact updated
        · have zero : p.refcount = 0 := by omega
          simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
            refcountDecAndTest, branch, branchCmp, CounterWindow.branch_run,
            CounterWindow.branchCmp_run, hd, hp, zero,
            StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
            CounterWindow.except_ok_bind, CounterWindow.except_pure,
            unsupported, AmbientM.unsupported] at hr
          cases hr

/-- Snapshot list deletion changes only allowed-IP links in saved peer records. -/
theorem listDel_view (id : NodeId) : SameView view (listDel id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hd:w.dev with
  | none=>simp [listDel,getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
  | some d=>
    obtain ⟨y,u,b,hu,_,hk⟩ := (total_iff_run_ambient _ _ _).mp
      (AllowedIps.listDel_wp w d hd id) w ambient rfl
    have he := hu.symm.trans hr
    cases he
    have hs : state (AllowedIps.unlisted d id)=state d := by
      unfold state; congr 1; funext q
      rw [AllowedIps.unlisted_get]
      cases d.peers[q]? <;> rfl
    simpa [view,hd,hs] using congrArg view hk

theorem removeByPeer_view (pid : PeerId) : SameView view (removeByPeer pid) := by

  rw [← AllowedIps.removeByPeerWithStep_eq]
  apply SameView.of_wp
  intro s
  let P := fun w : WGWorld => view w = s
  have read : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_spec (fun t => t = s) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  have step (id : NodeId) : Preserves P (AllowedIps.removeStep id) := by
    unfold AllowedIps.removeStep
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .removeListIter true) P)
    intro _
    apply preserves_bind (SameView.wp (listDel_view id) (fun t => t = s))
    intro _
    exact SameView.wp (node (project := fun w => w) (removeNodeBody_sameNode id))
      (fun t => t = s)
  unfold AllowedIps.removeByPeerWithStep
  apply preserves_bind read
  intro p
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .removeListEmpty p.allowedipsList.isEmpty) P)
  intro empty
  cases empty with
  | true => exact preserves_pure _
  | false =>
    apply preserves_bind (modifyDev_spec (fun t => t = s)
      (fun d => {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}})
      (fun _ => rfl))
    intro _
    apply preserves_bind (list_view_spec view (fun t => t = s) p.allowedipsList ()
      (fun id _ => AllowedIps.removeStep id) (fun id _ => step id))
    intro _
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .removeListIter false) P)
    intro _
    exact preserves_pure _

/-- Table removal precedes the fresh dead setter. Its temporary absence is
contained inside this exact source cut. -/
def killRows (pid : PeerId) : WG.M Unit := do
  modifyDev fun d=>{d with peerHashtable:=d.peerHashtable.filter (·.2!=pid)}
  setPeer pid {(←getPeer pid) with isDead:=true}

theorem killRows_view (pid : PeerId) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((killRows pid).run w).run ambient=.ok (((),v),ambient')) :
    view v=(view w).map (fun s=>s.kill pid) := by
  cases hd:w.dev with
  | none=>simp [killRows,modifyDev,getPeer,getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
  | some d=>
    cases hp:d.peers[pid]? with
    | none=>simp [killRows,modifyDev,getPeer,getDev,hd,hp,invariant,AmbientM.invariant] at hr; cases hr
    | some p=>
      simp [killRows,modifyDev,getPeer,getDev,setPeer,hd,hp] at hr
      rcases hr with ⟨rfl,rfl⟩
      simp only [view,hd,Option.map_some,Option.some.injEq]
      unfold state State.kill
      congr 1; funext q
      by_cases h:pid=q
      · subst q; simp [hp,cell]
      · simp [Std.TreeMap.getElem?_insert,h]

theorem peerMakeDead_preserves (pid : PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient) (hi : Inv w)
    (hr : ((peerMakeDead pid).run w).run ambient=.ok (((),v),ambient')) : Inv v := by
  have factor : peerMakeDead pid=(do
      modifyDev fun d=>{d with peerList:=d.peerList.filter (·!=pid)}
      removeByPeer pid
      _ ← branch .pubkeyRemoveHashed ((← getDev).peerHashtable.any (·.2 == pid))
      killRows pid) := rfl
  have hm := modifyDev_spec (fun v => ∀s,v=some s → s.Inv)
    (fun d=>{d with peerList:=d.peerList.filter (·!=pid)}) (fun _=>rfl)
  have hb := (removeByPeer_view pid).wp (fun v => ∀s,v=some s → s.Inv)
  have hk : Hoare (killRows pid) Inv (fun _ => Inv) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u ambientU x b ambientB hu hrun
    cases x
    have hv := killRows_view pid u b ambientU ambientB hrun
    intro s hs
    rw [hv] at hs
    obtain ⟨old,ho,he⟩:=Option.map_eq_some_iff.mp hs
    subst s
    exact State.Inv.kill (hu old ho) pid
  unfold Hoare at hk
  have hs : Hoare (peerMakeDead pid) Inv (fun _ => Inv) := by
    rw [factor]
    apply preserves_bind hm
    intro _
    apply preserves_bind hb
    intro _
    have getter : Preserves Inv getDev := by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro u a d out b hu hrun
      cases hd : u.dev with
      | none =>
        simp [getDev, hd, invariant, AmbientM.invariant] at hrun
        cases hrun
      | some saved =>
        simp [getDev, hd] at hrun
        rcases hrun with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hu
    apply preserves_bind getter
    intro d
    apply preserves_bind (hoare_liftAmbient
      (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid))) Inv)
    intro _
    exact hk
  exact (hoare_iff_run_ambient _ _ _).mp hs w ambient () v ambient' hi hr

/-- Successful fresh owner store-back cannot redirect a handshake's self word.
The peer borrow and owner setter may alias; the setter rereads its owner. -/
theorem acquireOwner_preserves (owner : IndexOwner) (w v : WGWorld) (result : Option PeerId) (ambient ambient' : Ambient)
    (hi : Inv w) (hr : ((Affiliation.acquireOwner owner).run w).run ambient=.ok ((result,v),ambient')) : Inv v := by
  have ac:=Affiliation.acquireOwner_acquisition owner w v result ambient ambient' hr
  have facts:=ac.facts
  obtain ⟨word,a,b,ambientA,ambientB,read,borrow,store⟩:=ac
  have ha := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerWord_preserves owner (fun u => view u = view w))
    w ambient word a ambientA rfl read
  have hb := (ProjectedAction.iff_run_ambient _ _ _).mp
    (peerGetMaybeZero_view word) a ambientA result b ambientB borrow
  cases owner with
  | keypair kid=>
    have frame : SameView view (IndexOwner.setPeerWord (.keypair kid) result) := by
      apply SameView.of_wp; intro s
      have hg:=(getKeypair_view kid).wp (fun t=>t=s)
      have hs:=fun k=>(setKeypair_view kid k).wp (fun t=>t=s)
      unfold IndexOwner.setPeerWord
      apply hoare_bind _ _ hg
      intro k
      exact hs {k with peer := result}
    have hv:=(ProjectedAction.iff_run_ambient _ _ _).mp frame b ambientB () v ambient' store
    intro s hs; exact hi s (by simpa [hv,hb,ha] using hs)
  | handshake pid=>
    have hw : Self result pid := by
      rcases facts.1 with eq|eq
      · exact Or.inl eq
      · cases hd:w.dev with
        | none=>simp [Affiliation.wordAt,Affiliation.view,hd] at eq
        | some d=>
          cases hp:d.peers[pid]? with
          | none=>simp [Affiliation.wordAt,Affiliation.view,Affiliation.state,Affiliation.State.word,hd,hp] at eq
          | some p=>
            have he : p.handshakeEntryPeer=result := by
              simpa [Affiliation.wordAt,Affiliation.view,Affiliation.state,Affiliation.State.word,Affiliation.peerCell,hd,hp] using eq
            exact he ▸ (hi (state d) (by simp [view,hd])).self pid (cell p) (by simp [state,hp])
    have hv:=word_effect pid result b v ambientB ambient' store
    intro s hs
    rw [hv,hb,ha] at hs
    obtain ⟨old,ho,he⟩:=Option.map_eq_some_iff.mp hs
    subst s; exact (hi old ho).setWord pid result hw

end Leanux.Proofs.WG.ConfiguredIdentity
