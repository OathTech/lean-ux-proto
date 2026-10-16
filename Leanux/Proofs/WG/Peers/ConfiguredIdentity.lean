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
    (stamp : p.stamp=old.stamp) (key : p.static=old.static) (word : Self p.word pid)
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
  mvcgen [getPeer,getDev,invariant,AmbientM.invariant]
  all_goals simp_all [view,state]

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
  apply SameView.of_wp; intro s
  have hg:=getPeer_spec (fun t=>t=s) pid
  have hs:=setPeer_spec (fun t=>t=s) pid
  mvcgen [precomputeStaticStatic,requireNotPending,hg,hs,getDev,branch,invariant,AmbientM.branch,AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view]

theorem cacheReset (pid : PeerId) : SameView view (dstCacheReset pid) := by
  apply SameView.of_wp; intro s
  have hg:=getPeer_spec (fun t=>t=s) pid
  have hs:=setPeer_spec (fun t=>t=s) pid
  have hc {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => view w = s) (fun _ w => view w = s) :=
    hoare_liftAmbient a _
  unfold Hoare at hc
  mvcgen [-Std.Do.Spec.monadLift_StateT,dstCacheReset,hg,hs,hc,hiddenJiffies,getAmbient]

theorem resetHandshake (pid : PeerId) : SameView view (resetLastSentHandshake pid) := by
  apply SameView.of_wp; intro s
  have hg:=getPeer_spec (fun t=>t=s) pid
  have hs:=setPeer_spec (fun t=>t=s) pid
  have ht {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => view w = s) (fun _ w => view w = s) :=
    hoare_liftAmbient a _
  unfold Hoare at ht
  mvcgen [-Std.Do.Spec.monadLift_StateT,resetLastSentHandshake,hg,hs,ht,hiddenClock64]

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
    mvcgen [hg,hs,hp,branch,AmbientM.branch]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [view]
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
  simp only [view,publishRow,modifyDev,Option.map_map,Function.comp_def]
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
  have proof : ⦃fun u=>⌜view u=view w⌝⦄ peerCreate key psk
      ⦃⇓? result u=>⌜Inv u ∧ ∀pid,result=.ok pid → ∃s p,view u=some s ∧ s.peers pid=some p ∧ p.static=key⌝⦄ := by
    rw [←Peers.peerCreateFactored_eq]
    have hc:=fun pid=>core_spec pid key
    have hi:=fun pid=>init_creating pid key psk
    have hd:=fun pid=>(cacheReset pid).wp (Creating pid key)
    have hh:=fun pid=>(resetHandshake pid).wp (Creating pid key)
    have hp:=fun pid=>publishRow_spec pid key
    dsimp only [publishRow] at hp
    have hg : ⦃fun u => ⌜view u = view w⌝⦄ getDev
        ⦃⇓? d u => ⌜view u = view w ∧ some (state d) = view w⌝⦄ := by
      mvcgen [getDev,invariant,AmbientM.invariant]
      all_goals simp_all [view]
    have ha {α : Type} (a : AmbientM α) :
        Hoare (MonadLift.monadLift a : WG.M α)
          (fun u => view u = view w) (fun _ u => view u = view w) :=
      hoare_liftAmbient a _
    unfold Hoare at ha
    mvcgen [-Std.Do.Spec.monadLift_StateT,Peers.peerCreateFactored,hc,hi,hd,hh,hp,hg,ha,hiddenAlloc,branch,branchCmp,invariant,AmbientM.branch,AmbientM.branchCmp,AmbientM.invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [Inv,InvExcept]
    all_goals
      rename_i hview hget hmax hbranch halloc hnomem hmore hdst hlast
      exact ⟨_, hget.2.symm, rfl⟩
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
    (fun s => by cases h : (project s).dev <;> simp [view,wgStoreView,h,state])

theorem getKeypair_view (id : KeypairId) : SameView view (getKeypair id) := by
  apply SameView.of_wp; intro s
  mvcgen [getKeypair,getDev,invariant,AmbientM.invariant]

theorem setKeypair_view (id : KeypairId) (k : Keypair) : SameView view (setKeypair id k) := by
  apply SameView.of_wp; intro s
  simpa only [setKeypair] using modifyDev_spec (fun v=>v=s)
    (fun d=>{d with keypairs:=d.keypairs.insert id k}) (fun _=>rfl)

theorem handshakeZero_view (pid : PeerId) : SameView view (handshakeZero pid) := by
  apply SameView.of_wp; intro s
  have hg:=getPeer_spec (fun t=>t=s) pid
  have hs:=setPeer_spec (fun t=>t=s) pid
  mvcgen [handshakeZero,hg,hs]

theorem keypairPut_view (kp : Option KeypairId) (unreference : Bool) : SameView view (keypairPut kp unreference) := by
  apply SameView.of_wp; intro s
  have hg:=fun id=>(getKeypair_view id).wp (fun t=>t=s)
  have hs:=fun id k=>(setKeypair_view id k).wp (fun t=>t=s)
  have hi {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => view w = s) (fun _ w => view w = s) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa only [view,hd,Option.map_some,state] using hg
  have hd:=fun owner=>indexOwner_peerDeref_preserves owner (fun w=>view w=s)
  unfold Hoare at hi
  unfold Preserves Hoare at hd
  have hm:=fun id=>modifyDev_spec (fun t=>t=s) (fun d=>{d with keypairs:=d.keypairs.erase id}) (fun _=>rfl)
  mvcgen [keypairPut,hg,hs,hi,hd,hm,refcountDecAndTest,branch,branchCmp,invariant,unsupported,
    AmbientM.branch,AmbientM.branchCmp,AmbientM.invariant,AmbientM.unsupported]

theorem modifyPeer_view (pid : PeerId) (f : Peer→Peer) (hf : ∀p,cell (f p)=cell p) :
    SameView view ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by
  apply SameView.of_wp; intro s
  have hg:=getPeer_spec (fun t=>t=s) pid
  have hs:=setPeer_spec (fun t=>t=s) pid
  change ⦃fun w => ⌜view w = s⌝⦄ (do setPeer pid (f (← getPeer pid))) ⦃⇓? _ w => ⌜view w = s⌝⦄
  mvcgen [hg,hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [hf]
  all_goals grind only

theorem addNewKeypair_view (pid : PeerId) (kp : KeypairId) : SameView view (addNewKeypair pid kp) := by
  apply SameView.of_wp; intro s
  have hg:=getPeer_spec (fun t=>t=s) pid
  have hs:=setPeer_spec (fun t=>t=s) pid
  have hk:=fun id=>(getKeypair_view id).wp (fun t=>t=s)
  have hp:=fun id b=>(keypairPut_view id b).wp (fun t=>t=s)
  have hm := fun f hf=>(modifyPeer_view pid f hf).wp (fun t=>t=s)
  mvcgen [addNewKeypair,hg,hs,hk,hp,hm,branch,AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view,cell]

/-- Retirement removes a slot, and need not remove its stale hash rows. -/
theorem erase_inv (d : Device) (pid dropped : Nat) (hi : (state d).Inv) :
    (state {d with txDropped:=dropped,peers:=d.peers.erase pid}).Inv := by
  have he : state {d with txDropped:=dropped,peers:=d.peers.erase pid}=(state d).put pid none := by
    unfold state State.put; congr 1; funext q
    by_cases h:pid=q <;> simp [Std.TreeMap.getElem?_erase,h]
  rw [he]; exact hi.erase pid

theorem peerPut_preserves (peer : Option PeerId) :
    ⦃fun w=>⌜Inv w⌝⦄ peerPut peer ⦃⇓? _ w=>⌜Inv w⌝⦄ := by
  let P := fun v : Option State=>∀s,v=some s→s.Inv
  have hg:=getPeer_spec P
  have hs:=setPeer_spec P
  have hi {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) Inv (fun _ => Inv) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa only [Inv,InvExcept,view,hd,Option.map_some,state] using hg
  have ha {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) Inv (fun _ => Inv) :=
    hoare_liftAmbient a _
  unfold Hoare at hi ha
  have hm (pid dropped : Nat) :
      ⦃fun w=>⌜Inv w⌝⦄ modifyDev (fun d=>{d with txDropped:=d.txDropped+dropped,peers:=d.peers.erase pid})
      ⦃⇓? _ w=>⌜Inv w⌝⦄ := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hw hr
    cases hr
    intro s he
    cases hd:w.dev with
    | none=>simp [view,modifyDev,hd] at he
    | some d=>
      have h := hw (state d) (by simp [view,hd])
      have eq : s=state {d with txDropped:=d.txDropped+dropped,peers:=d.peers.erase pid} := by
        simpa [view,modifyDev,hd] using he.symm
      subst s; exact erase_inv d pid _ h
  mvcgen [-Std.Do.Spec.monadLift_StateT,peerPut,requireNotPending,hg,hs,hi,hm,ha,refcountDecAndTest,retirePeerUnits,
    branch,branchCmp,unsupported,invariant,AmbientM.branch,AmbientM.branchCmp,AmbientM.unsupported,AmbientM.invariant]

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
  apply SameView.of_wp; intro s
  have hg:=getPeer_spec (fun t=>t=s) pid
  have hlst:=fun id=>(listDel_view id).wp (fun t=>t=s)
  have hn:=fun nodeId=>(node (project := fun w => w) (removeNodeBody_sameNode nodeId)).wp (fun t=>t=s)
  have hm:=modifyDev_spec (fun t=>t=s) (fun d=>{d with peerAllowedips:={d.peerAllowedips with seq:=d.peerAllowedips.seq+1}}) (fun _=>rfl)
  have hl (α β : Type):=list_view_spec (m := AmbientM) view (α:=α) (β:=β) (fun t=>t=s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,
    AllowedIps.removeByPeerWithStep,AllowedIps.removeStep,hg,hlst,hn,hm,branch,AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view]

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
    unfold Hoare
    mvcgen [hm,hb,hk,getDev,branch,invariant,AmbientM.branch,AmbientM.invariant]
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
      mvcgen [IndexOwner.setPeerWord,hg,hs]
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
