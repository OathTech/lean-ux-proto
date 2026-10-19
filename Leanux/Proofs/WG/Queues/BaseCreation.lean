import Leanux.Proofs.WG.Queues.DecryptCarrier
import Leanux.Proofs.WG.Peers.ConfiguredIdentity
import Leanux.Proofs.WG.Queues.WorkReservations

/-! The allocation's initial reference is a source-owned reservation. It is
created before list publication; membership alone never supplies funding. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCreation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

def owner (w : WGWorld) (d : Device) : Owner :=
  ⟨d.ifindex,d.nextPeer,w.peerCounter+1⟩

theorem frontier_vacant (hi : ConfiguredIdentity.Inv w) (hd : w.dev = some d) :
    d.peers[d.nextPeer]? = none := by
  cases hp : d.peers[d.nextPeer]? with
  | none => rfl
  | some p =>
    have bound := (hi (ConfiguredIdentity.state d) (by simp [ConfiguredIdentity.view,hd])).bounded
      d.nextPeer (ConfiguredIdentity.cell p) (by simp [ConfiguredIdentity.state,hp])
    exact False.elim (Nat.lt_irrefl _ bound)

theorem vacant_demand (hi : Protected cs loans w) (hd : w.dev = some d)
    (vacant : d.peers[pid]? = none) (o : Owner) (slot : o.slot = pid) :
    demand cs loans o = 0 := by
  have bound := hi o
  have zero : balance w o = 0 := by
    simp [balance,resident,hd,slot,vacant]
  rw [zero] at bound
  omega

private theorem core_balance (hd : w.dev = some d) (vacant : d.peers[d.nextPeer]? = none)
    (key : Key) (o : Owner) :
    balance (Peers.creationCoreWorld w d.nextPeer key) o =
      if o = owner w d then 1 else balance w o := by
  rcases o with ⟨epoch,slot,stamp⟩
  by_cases he : d.ifindex = epoch
  · subst epoch
    by_cases hs : d.nextPeer = slot
    · subst slot
      by_cases ht : w.peerCounter+1 = stamp
      · subst stamp
        simp [balance,resident,Peers.creationCoreWorld,Peers.createdPeer,owner,hd]
      · simp [balance,resident,Peers.creationCoreWorld,Peers.createdPeer,owner,hd,vacant,ht,Ne.symm ht]
    · simp [balance,resident,Peers.creationCoreWorld,Peers.createdPeer,owner,hd,
        Std.TreeMap.getElem?_insert,hs,Ne.symm hs]
  · simp [balance,resident,Peers.creationCoreWorld,owner,hd,he,Ne.symm he]

theorem core_funded (hi : Protected cs loans w) (hd : w.dev = some d)
    (vacant : d.peers[d.nextPeer]? = none) (key : Key) :
    Protected cs (owner w d :: loans) (Peers.creationCoreWorld w d.nextPeer key) := by
  intro o
  rw [core_balance hd vacant key o]
  by_cases same : o = owner w d
  · subst o
    have zero := vacant_demand hi hd vacant (owner w d) rfl
    simp only [demand] at zero ⊢
    simp [show charges cs (owner w d) = 0 by omega,
      show loans.count (owner w d) = 0 by omega]
  · simp only [ite_eq_right same]
    simpa [demand,List.count_cons,Ne.symm same] using hi o

private theorem queued_absent (hi : Protected cs loans w) (hd : w.dev = some d)
    (vacant : d.peers[d.nextPeer]? = none) (c : Carrier) (hc : c ∈ cs)
    (eq : c.owner = owner w d) (phase : c.phase = .queued) : False := by
  have zero := vacant_demand hi hd vacant (owner w d) rfl
  have member : c ∈ cs.filter (fun x => x.owner == owner w d && x.phase.charged) :=
    List.mem_filter.mpr ⟨hc,by simp [eq,phase,Phase.charged]⟩
  have positive := List.length_pos_of_mem member
  change 0 < charges cs (owner w d) at positive
  unfold demand at zero
  omega

theorem core_carrier (hi : CarrierState cs loans w) (hd : w.dev = some d)
    (vacant : d.peers[d.nextPeer]? = none) (key : Key) :
    CarrierState cs (owner w d :: loans) (Peers.creationCoreWorld w d.nextPeer key) := by
  let v := Peers.creationCoreWorld w d.nextPeer key
  have rx : rxView v = rxView w := by simp [v,rxView,Peers.creationCoreWorld,hd]
  refine ⟨inventory_view hi.inventory rx,?_,core_funded hi.funded hd vacant key,?_,?_⟩
  · intro out pid p id hout hp
    have same : out = {d with nextPeer := d.nextPeer+1, peers := d.peers.insert d.nextPeer (Peers.createdPeer key (w.peerCounter+1))} := by
      simpa [v,Peers.creationCoreWorld,hd] using hout.symm
    subst out
    by_cases selected : d.nextPeer = pid
    · subst pid
      have peq : p = Peers.createdPeer key (w.peerCounter+1) := by simpa using hp.symm
      subst p
      have empty : (cs.filter (fun c => c.packet == ⟨d.ifindex,id⟩ &&
          c.owner == owner w d && c.phase == .queued)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c hc
        intro positive
        simp only [Bool.and_eq_true,beq_iff_eq] at positive
        exact queued_absent hi.funded hd vacant c hc positive.1.2 positive.2
      simpa [Peers.createdPeer,PrevQueue.all,owner,empty] using congrArg List.length empty.symm
    · exact hi.queues d pid p id hd (by simpa [Std.TreeMap.getElem?_insert,selected] using hp)
  · intro out id pkt hout hp other k hother hk
    have same : out = {d with nextPeer := d.nextPeer+1, peers := d.peers.insert d.nextPeer (Peers.createdPeer key (w.peerCounter+1))} := by
      simpa [v,Peers.creationCoreWorld,hd] using hout.symm
    have same' : other = out := Option.some.inj (hother.symm.trans hout)
    subst other; subst out
    exact hi.keys.1 d id pkt hd hp d k hd hk
  · intro pid out p kid hout hp hc other k hother hk
    have same : out = {d with nextPeer := d.nextPeer+1, peers := d.peers.insert d.nextPeer (Peers.createdPeer key (w.peerCounter+1))} := by
      simpa [v,Peers.creationCoreWorld,hd] using hout.symm
    have same' : other = out := Option.some.inj (hother.symm.trans hout)
    subst other; subst out
    by_cases selected : d.nextPeer = pid
    · subst pid
      have peq : p = Peers.createdPeer key (w.peerCounter+1) := by simpa using hp.symm
      subst p
      cases hc
    · exact hi.keys.2 pid d p kid hd
        (by simpa [Std.TreeMap.getElem?_insert,selected] using hp) hc d k hd hk

theorem core_stable (hi : StableRx cs w) (hd : w.dev = some d) (key : Key) :
    StableRx cs (Peers.creationCoreWorld w d.nextPeer key) := by
  have packets : ∀ p, packetAt (Peers.creationCoreWorld w d.nextPeer key) p = packetAt w p := by
    intro p; simp [packetAt,Peers.creationCoreWorld,hd]
  refine ⟨hi.queued,?_,?_⟩
  · intro out hout
    have same : out = {d with nextPeer := d.nextPeer+1, peers := d.peers.insert d.nextPeer (Peers.createdPeer key (w.peerCounter+1))} := by
      simpa [Peers.creationCoreWorld,hd] using hout.symm
    subst out
    simpa only [uncrypted,packets] using hi.ring d hd
  · intro out pid p id hout hp cold head
    have same : out = {d with nextPeer := d.nextPeer+1, peers := d.peers.insert d.nextPeer (Peers.createdPeer key (w.peerCounter+1))} := by
      simpa [Peers.creationCoreWorld,hd] using hout.symm
    subst out
    by_cases selected : d.nextPeer = pid
    · subst pid
      have peq : p = Peers.createdPeer key (w.peerCounter+1) := by simpa using hp.symm
      subst p
      cases head
    · exact hi.cold d pid p id hd
        (by simpa [Std.TreeMap.getElem?_insert,selected] using hp) cold head

theorem core_normal (hi : CarrierState cs loans w) (hs : StableRx cs w)
    (configured : ConfiguredIdentity.Inv w) (hd : w.dev = some d) (key : Key)
    (a b : Ambient)
    (run : ((Peers.peerCreateCore d.nextPeer key).run w).run a = .ok (((),v),b)) :
    CarrierState cs (owner w d :: loans) v ∧ StableRx cs v ∧
      resident v (owner w d) = some (Peers.createdPeer key (w.peerCounter+1)) := by
  rw [Peers.peerCreateCore_run] at run
  cases run
  exact ⟨core_carrier hi hd (frontier_vacant configured hd) key,core_stable hs hd key,
    by simp [resident,owner,Peers.creationCoreWorld,hd,Peers.createdPeer]⟩


private def cell (p : Peer) :=
  (p.internalId,p.refcount,p.rxQueue,p.napiScheduled,p.keypairCurrent)
private def fields (w : WGWorld) :=
  (w.dev.map (fun d => (d.ifindex,d.decryptQueue,d.rxSkbs,d.keypairs,d.peerList)),
   fun pid : PeerId => (w.dev.bind fun d => d.peers[pid]?).map cell)

private theorem fields_transport (same : fields v = fields w) :
    DecryptCarrier.decryptView v = DecryptCarrier.decryptView w ∧
      v.dev.map Device.peerList = w.dev.map Device.peerList := by
  have base := congrArg Prod.fst same
  have peers := congrArg Prod.snd same
  have common : ∀ pid, (v.dev.bind fun d => d.peers[pid]?).map cell =
      (w.dev.bind fun d => d.peers[pid]?).map cell := congrFun peers
  cases hv : v.dev <;> cases hw : w.dev
  all_goals simp only [fields,hv,hw,Option.map_none,Option.map_some] at base
  all_goals try contradiction
  case none.none =>
    unfold DecryptCarrier.decryptView carrierView stableView keyView
    unfold peerView rxView RxRing.nativeCell keyWords currentCells
    simp [hv,hw]
  case some.some a b =>
    have eq := Option.some.inj base
    have epoch := congrArg Prod.fst eq
    have ring := congrArg (fun x => x.2.1) eq
    have rx := congrArg (fun x => x.2.2.1) eq
    have keys := congrArg (fun x => x.2.2.2.1) eq
    have list := congrArg (fun x => x.2.2.2.2) eq
    dsimp only at epoch ring rx keys list
    have credit : peerView v = peerView w := by
      unfold peerView
      simp only [hv,hw,Option.map_some,epoch,Option.bind_some]
      apply congrArg (Prod.mk (some b.ifindex))
      funext pid
      simpa only [cell,Option.map_map,Function.comp_def,hv,hw,Option.bind_some] using
        congrArg (Option.map (fun x => (x.1,x.2.1,x.2.2.1))) (common pid)
    have current : currentCells v = currentCells w := by
      unfold currentCells currentCell
      funext pid
      simpa only [cell,Option.map_map,Function.comp_def] using
        congrArg (Option.map (fun x => (x.1,x.2.2.2.2))) (common pid)
    have cold : (fun pid : PeerId => (v.dev.bind fun d => d.peers[pid]?).map
        (fun p => (p.rxQueue,p.napiScheduled))) =
      (fun pid : PeerId => (w.dev.bind fun d => d.peers[pid]?).map
        (fun p => (p.rxQueue,p.napiScheduled))) := by
      funext pid
      simpa only [cell,Option.map_map,Function.comp_def] using
        congrArg (Option.map (fun x => (x.2.2.1,x.2.2.2.1))) (common pid)
    unfold DecryptCarrier.decryptView carrierView stableView keyView
    rw [credit,current,cold]
    unfold RxRing.nativeCell rxView keyWords
    simp only [hv,hw,Option.map_some,Option.bind_some,epoch,ring,rx,keys,list]
    exact ⟨True.intro,True.intro⟩

private theorem getPeer_spec (P : _ → Prop) (pid : PeerId) :
    Hoare (getPeer pid) (fun w => P (fields w))
      (fun p w => P (fields w) ∧ (fields w).2 pid = some (cell p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi hr
  obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal pid w v p a b hr
  exact ⟨hi,by simp [fields,hd,hp]⟩

private theorem setPeer_spec (P : _ → Prop) (pid : PeerId) (p : Peer) :
    Hoare (setPeer pid p) (fun w => P (fields w) ∧ (fields w).2 pid = some (cell p))
      (fun _ w => P (fields w)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi hr
  cases hd : w.dev with
  | none => simp [fields,hd] at hi
  | some d =>
    obtain ⟨old,ho,he⟩ := Option.map_eq_some_iff.mp (by simpa [fields,hd] using hi.2)
    have eq : fields {w with dev := some {d with peers := d.peers.insert pid p}} = fields w := by
      simp only [fields,hd,Option.map_some,Option.bind_some]
      congr 1
      funext q
      by_cases chosen : pid = q
      · subst q; simp [ho,he]
      · simp [Std.TreeMap.getElem?_insert,chosen]
    cases hr
    simpa only [setPeer,modifyDev,hd,Option.map_some,eq] using hi.1

private theorem sameWG {α : Type} {a : WG.M α} (ha : SameWGStore a) : SameView fields a :=
  ha.of_factor (fun s : WGStoreView =>
    (s.dev.map (fun d => (d.ifindex,d.decryptQueue,d.rxSkbs,d.keypairs,d.peerList)),
      fun pid : PeerId => (s.dev.bind fun d => d.peers[pid]?).map cell)) _ (fun _ => rfl)

private theorem read_bind (initial : _) (pid : PeerId) (f : Peer → WG.M α)
    (hf : ∀ p, initial.2 pid = some (cell p) → Preserves (fun w => fields w = initial) (f p)) :
    Preserves (fun w => fields w = initial) (getPeer pid >>= f) := by
  apply hoare_bind _ _ (getPeer_spec (fun s => s = initial) pid)
  intro p
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b h hr
  have saved := h.2
  rw [h.1] at saved
  exact (hoare_iff_run_ambient _ _ _).mp (hf p saved) w a x v b h.1 hr

private theorem set_saved (initial : _) (pid : PeerId) (p : Peer)
    (hp : initial.2 pid = some (cell p)) : Preserves (fun w => fields w = initial) (setPeer pid p) := by
  apply hoare_consequence (setPeer_spec (fun s => s = initial) pid p)
  · intro w h; exact ⟨h,by rw [h]; exact hp⟩
  · exact fun _ _ h => h

macro "base_init_step " initial:ident : tactic => `(tactic| first
  | (env_bind_head getPeer; apply read_bind $initial; intro p hp)
  | (rx_retention_head setPeer; apply set_saved $initial; assumption)
  | (rx_retention_head getPeer; exact hoare_consequence (getPeer_spec (fun s => s = $initial) _)
      (fun _ h => h) (fun _ _ h => h.1))
  | (rx_retention_head getDev; exact (sameWG getDev_sameWGStore).wp (fun s => s = $initial))
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

private theorem dstCacheReset_fields (pid : PeerId) : SameView fields (dstCacheReset pid) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' base_init_step initial

private theorem resetLast_fields (pid : PeerId) : SameView fields (resetLastSentHandshake pid) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' base_init_step initial

private theorem precompute_fields (pid : PeerId) : SameView fields (precomputeStaticStatic pid) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold precomputeStaticStatic
  simp (config := {zeta := false}) only [requireNotPending,branch]
  repeat' base_init_step initial

private theorem handshakeInit_fields (pid : PeerId) (psk : Option Key) :
    SameView fields (handshakeInit pid psk) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold handshakeInit IndexOwner.setPeerWord
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head precomputeStaticStatic;
       exact (precompute_fields _).wp (fun s => s = initial))
    | base_init_step initial


/-- The existing initializer tail, ending at the real list publication. -/
def finish (pid : PeerId) (key : Key) (psk : Option Key) : WG.M Unit := do
  dstCacheReset pid
  handshakeInit pid psk
  resetLastSentHandshake pid
  ConfiguredIdentity.publishRow pid key

theorem peerCreate_factor (key : Key) (psk : Option Key) : peerCreate key psk = (do
    let d ← getDev
    if ← branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE then
      return .error (-ENOMEM)
    if ← branch .peerCreateNoMem !(← hiddenAlloc .kmemCacheZallocPeer) then return .error (-ENOMEM)
    if ← branch .peerCreateDstCacheFail false then return .error (-ENOMEM)
    Peers.peerCreateCore d.nextPeer key
    finish d.nextPeer key psk
    pure (.ok d.nextPeer)) := by
  rw [← Peers.peerCreateFactored_eq]
  simp only [Peers.peerCreateFactored,finish,ConfiguredIdentity.publishRow,bind_assoc]

theorem finish_normal (pid : PeerId) (key : Key) (psk : Option Key) (w v : WGWorld)
    (a b : Ambient) (run : ((finish pid key psk).run w).run a = .ok (((),v),b)) :
    DecryptCarrier.decryptView v = DecryptCarrier.decryptView w ∧
      v.dev.map Device.peerList = (w.dev.map Device.peerList).map (fun xs => xs ++ [pid]) := by
  unfold finish at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,x,ax,hx,rest⟩ := run; cases u
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,y,ay,hy,rest⟩ := rest; cases u
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,z,az,hz,done⟩ := rest; cases u
  have xfields := (ProjectedAction.iff_run_ambient _ _ _).mp (dstCacheReset_fields pid) w a () x ax hx
  have yfields := (ProjectedAction.iff_run_ambient _ _ _).mp (handshakeInit_fields pid psk) x ax () y ay hy
  have zfields := (ProjectedAction.iff_run_ambient _ _ _).mp (resetLast_fields pid) y ay () z az hz
  have same := fields_transport (zfields.trans (yfields.trans xfields))
  cases done
  constructor
  · refine Eq.trans ?_ same.1
    unfold DecryptCarrier.decryptView carrierView stableView
    unfold keyView peerView rxView keyWords currentCells RxRing.nativeCell
    cases hd : z.dev <;> simp [hd]
  · simpa only [ConfiguredIdentity.publishRow,modifyDev,Option.map_map,Function.comp_def] using
      congrArg (Option.map (fun xs => xs ++ [pid])) same.2

/-- A successful initializer has appended the allocated slot, and retains
exactly the initial reference funded at the earlier core cut. -/
theorem finish_funded (pid : PeerId) (key : Key) (psk : Option Key)
    (hi : CarrierState cs loans w) (hs : StableRx cs w) (a b : Ambient)
    (run : ((finish pid key psk).run w).run a = .ok (((),v),b)) :
    CarrierState cs loans v ∧ StableRx cs v ∧
      v.dev.map Device.peerList = (w.dev.map Device.peerList).map (fun xs => xs ++ [pid]) := by
  have same := finish_normal pid key psk w v a b run
  exact ⟨hi.view (congrArg Prod.fst same.1), hs.view (congrArg Prod.snd same.1),same.2⟩

/-- Normal errno returns preserve the supplied ledger. Actual successful
creation adds exactly one stamped base reservation and appends that slot to
its original device list; no list-membership funding premise is used. -/
theorem peerCreate_normal (key : Key) (psk : Option Key)
    (hi : CarrierState cs loans w) (hs : StableRx cs w) (configured : ConfiguredIdentity.Inv w)
    (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    match result with
    | .error _ => CarrierState cs loans v ∧ StableRx cs v
    | .ok pid => ∃ d, w.dev = some d ∧ pid = d.nextPeer ∧
        CarrierState cs (owner w d :: loans) v ∧ StableRx cs v ∧
        v.dev.map Device.peerList = some (d.peerList ++ [pid]) := by
  let Q := fun (r : Except Int PeerId) (out : WGWorld) => match r with
    | .error _ => CarrierState cs loans out ∧ StableRx cs out
    | .ok pid => ∃ d, w.dev = some d ∧ pid = d.nextPeer ∧
        CarrierState cs (owner w d :: loans) out ∧ StableRx cs out ∧
        out.dev.map Device.peerList = some (d.peerList ++ [pid])
  have getter : Hoare getDev (fun u => u = w) (fun d u => u = w ∧ w.dev = some d) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro u aa d out bb hu hr
    subst u
    cases hd : w.dev with
    | none => simp [getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
    | some before =>
      simp [getDev,hd] at hr
      rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩
      exact ⟨rfl,rfl⟩
  have proof : Hoare (peerCreate key psk) (fun u => u = w) Q := by
    rw [peerCreate_factor]
    apply hoare_bind _ _ getter
    intro d
    let P := fun u => u = w ∧ w.dev = some d
    have ambient {α : Type} (act : AmbientM α) : Preserves P (monadLift act : WG.M α) :=
      hoare_liftAmbient act P
    have failure : Hoare (pure (.error (-ENOMEM)) : WG.M (Except Int PeerId)) P Q := by
      apply hoare_consequence (hoare_pure _ P)
      · exact fun _ h => h
      · intro r u h
        rcases h with ⟨rfl,hu,_⟩
        subst u
        exact ⟨hi,hs⟩
    apply hoare_bind _ _ (ambient (AmbientM.branchCmp .peerCreateMaxPeers
      (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE))
    intro maxPeers
    cases maxPeers with
    | true => exact failure
    | false =>
      apply hoare_bind _ _ (ambient (AmbientM.hiddenAlloc .kmemCacheZallocPeer))
      intro allocated
      apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateNoMem !allocated))
      intro noMem
      cases noMem with
      | true => exact failure
      | false =>
        apply hoare_bind _ _ (ambient (AmbientM.branch .peerCreateDstCacheFail false))
        intro cacheFailed
        cases cacheFailed with
        | true => exact failure
        | false =>
          have core : Hoare (Peers.peerCreateCore d.nextPeer key) P
              (fun _ u => w.dev = some d ∧ CarrierState cs (owner w d :: loans) u ∧
                StableRx cs u ∧ u.dev.map Device.peerList = some d.peerList) := by
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro u aa x out bb h hr
            rcases h with ⟨rfl,hd⟩
            cases x
            have fact := core_normal hi hs configured hd key aa bb hr
            rw [Peers.peerCreateCore_run] at hr
            cases hr
            exact ⟨hd,fact.1,fact.2.1,by simp [Peers.creationCoreWorld,hd]⟩
          apply hoare_bind _ _ core
          intro _
          have tail : Hoare (finish d.nextPeer key psk)
              (fun u => w.dev = some d ∧ CarrierState cs (owner w d :: loans) u ∧
                StableRx cs u ∧ u.dev.map Device.peerList = some d.peerList)
              (fun _ u => Q (.ok d.nextPeer) u) := by
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro u aa x out bb h hr
            cases x
            obtain ⟨hc,hstable,list⟩ := finish_funded d.nextPeer key psk h.2.1 h.2.2.1 aa bb hr
            exact ⟨d,h.1,rfl,hc,hstable,by simpa only [h.2.2.2,Option.map_some] using list⟩
          apply hoare_bind _ _ tail
          intro _
          apply hoare_consequence (hoare_pure (Except.ok d.nextPeer : Except Int PeerId) _)
          · exact fun _ h => h
          · intro r u h; rcases h with ⟨rfl,h⟩; exact h
  have out := (hoare_iff_run_ambient _ _ _).mp proof w a result v b rfl run
  cases result <;> exact out


/-- The ordered base ledger is supplied as already funded. Vacancy proves
its list cannot already name the allocated slot, even with arbitrary stamps. -/
theorem funded_list_fresh (hi : CarrierState cs (owners ++ loans) w)
    (hd : w.dev = some d) (vacant : d.peers[d.nextPeer]? = none)
    (list : d.peerList = owners.map Owner.slot) : d.nextPeer ∉ d.peerList := by
  rw [list]
  intro present
  obtain ⟨o,inside,slot⟩ := List.mem_map.mp present
  have zero := vacant_demand hi.funded hd vacant o slot
  have positive : 0 < owners.count o := List.count_pos_iff.mpr inside
  simp only [demand,List.count_append] at zero
  omega

/-- Successful creation appends its one base owner to an already funded list
account; the independent loans and all RX carriers remain protected. -/
theorem peerCreate_accounts (key : Key) (psk : Option Key)
    (hi : CarrierState cs (owners ++ loans) w) (hs : StableRx cs w)
    (configured : ConfiguredIdentity.Inv w) (hd : w.dev = some d)
    (list : d.peerList = owners.map Owner.slot) (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a = .ok ((.ok pid,v),b)) :
    pid = d.nextPeer ∧
      CarrierState cs ((owners ++ [owner w d]) ++ loans) v ∧ StableRx cs v ∧
      v.dev.map Device.peerList = some ((owners ++ [owner w d]).map Owner.slot) ∧
      pid ∉ d.peerList := by
  obtain ⟨before,hbefore,selected,hc,hstable,hlist⟩ :=
    peerCreate_normal key psk hi hs configured a b run
  have eq : before = d := Option.some.inj (hbefore.symm.trans hd)
  subst before
  have perm : (owner w d :: (owners ++ loans)).Perm ((owners ++ [owner w d]) ++ loans) := by
    simpa only [List.append_assoc,List.singleton_append] using
      (List.perm_middle : (owners ++ owner w d :: loans).Perm (owner w d :: (owners ++ loans))).symm
  refine ⟨selected,WorkReservations.carrier_loans_perm hc perm,hstable,?_,?_⟩
  · simpa only [List.map_append,List.map_cons,List.map_nil,owner,selected,←list] using hlist
  · rw [selected]
    exact funded_list_fresh hi hd (frontier_vacant configured hd) list

end Leanux.Proofs.WG.Queues.RxCredits.BaseCreation
