import Leanux.Proofs.WG.Queues.CurrentSlots
import Leanux.Proofs.WG.Packets.PublicationIngress

/-! Transport of the existing three-slot invariant through its exact fields.
The observation forgets packets, key validity, peer identity, and reference
counts. Deletion and nullable owner-word reduction are handled separately. -/
namespace Leanux.Proofs.WG.CurrentSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
open Lifetimes Affiliation

def slotCell (p : Peer) := (p.keypairCurrent,p.keypairPrevious,p.keypairNext)

def fields (w : WGWorld) := (w.dev.map (·.nextKeypairId),
  (fun pid : PeerId => (w.dev.bind fun d => d.peers[pid]?).map slotCell),
  Queues.RxCredits.keyWords w)

theorem inv_iff (w : WGWorld) : Inv w ↔
    ∀ d pid p kid, w.dev = some d → d.peers[pid]? = some p →
      (p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid) →
      kid < d.nextKeypairId ∧ ∀ key, d.keypairs[kid]? = some key → Compatible key.peer pid := by
  constructor
  · intro hi d pid p kid hd hp hs
    have h := hi (state d) (by simp [Affiliation.view,hd]) pid (peerCell p) kid
      (by simp [state,hp]) hs
    exact ⟨h.1,fun key hk => h.2 key.internalId key.peer (by simp [state,keyCell,hk])⟩
  · intro hi s hs pid p kid hp hslot
    obtain ⟨d,hd,rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨peer,resident,rfl⟩ := Option.map_eq_some_iff.mp hp
    have h := hi d pid peer kid hd resident hslot
    refine ⟨h.1,?_⟩
    intro stamp word hk
    obtain ⟨key,hkey,eq⟩ := Option.map_eq_some_iff.mp hk
    have hw : key.peer = word := congrArg Prod.snd eq
    simpa only [←hw] using h.2 key hkey

theorem fields_transport (hi : Inv w) (same : fields v = fields w) : Inv v := by
  apply (inv_iff v).mpr
  intro d pid p kid hd hp hs
  have front := congrArg Prod.fst same
  have slots := congrFun (congrArg (fun t => t.2.1) same) pid
  have words := congrFun (congrArg (fun t => t.2.2) same) kid
  have before : w.dev.map (·.nextKeypairId) = some d.nextKeypairId := by
    simpa only [fields,hd,Option.map_some] using front.symm
  obtain ⟨old,ho,hfront⟩ := Option.map_eq_some_iff.mp before
  have resident : (old.peers[pid]?).map slotCell = some (slotCell p) := by
    simpa only [fields,hd,ho,Option.bind_some,hp,Option.map_some] using slots.symm
  obtain ⟨q,hq,cells⟩ := Option.map_eq_some_iff.mp resident
  have selected : q.keypairCurrent = some kid ∨ q.keypairPrevious = some kid ∨ q.keypairNext = some kid := by
    have a := congrArg Prod.fst cells
    have b := congrArg (fun t => t.2.1) cells
    have c := congrArg (fun t => t.2.2) cells
    dsimp only [slotCell] at a b c
    simpa only [a,b,c] using hs
  have oldref := (inv_iff w).mp hi old pid q kid ho hq selected
  refine ⟨hfront ▸ oldref.1,?_⟩
  intro key hk
  have oldword : (old.keypairs[kid]?).map (·.peer) = some key.peer := by
    simpa only [fields,Queues.RxCredits.keyWords,hd,ho,Option.bind_some,hk,Option.map_some] using words.symm
  obtain ⟨oldkey,hold,hword⟩ := Option.map_eq_some_iff.mp oldword
  simpa only [hword] using oldref.2 oldkey hold

/-- The same observation transport works for arbitrary outer/product state. -/
theorem fields_preserves {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => fields (project s)) a) :
    Preserves (fun s => Inv (project s)) a := by
  apply hoare_consequence (ha.wp (fun f => ∃ w, Inv w ∧ fields w = f))
  · exact fun s hi => ⟨project s,hi,rfl⟩
  · intro _ s h
    obtain ⟨w,hi,he⟩ := h
    exact fields_transport hi he.symm

theorem slotWord (hi : SlotInv s) (owner : IndexOwner) (word : Option PeerId)
    (hw : word = none ∨ s.word owner = some word) : SlotInv (s.setWord owner word) := by
  intro pid p kid hp hs
  cases owner with
  | handshake q =>
    by_cases same : pid = q
    · subst pid
      simp only [State.setWord,ite_true] at hp
      obtain ⟨old,ho,rfl⟩ := Option.map_eq_some_iff.mp hp
      exact hi q old kid ho hs
    · exact hi pid p kid (by simpa [State.setWord,same] using hp) hs
  | keypair changed =>
    have old := hi pid p kid hp hs
    refine ⟨old.1,?_⟩
    intro stamp newword hk
    by_cases same : kid = changed
    · subst kid
      simp only [State.setWord,ite_true] at hk
      obtain ⟨key,hkey,eq⟩ := Option.map_eq_some_iff.mp hk
      have neweq : newword = word := (congrArg Prod.snd eq).symm
      subst newword
      rcases hw with rfl | hw
      · exact Or.inl rfl
      · have sameWord : word = key.2 := by simpa [State.word,hkey] using hw.symm
        rw [sameWord]
        exact old.2 key.1 key.2 hkey
    · exact old.2 stamp newword (by simpa [State.setWord,same] using hk)

theorem acquireOwner_preserves (owner : IndexOwner) : Preserves Inv (Affiliation.acquireOwner owner) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have facts := (Affiliation.acquireOwner_acquisition owner w v result a b hr).facts
  intro out hout
  rw [facts.2] at hout
  obtain ⟨s,hs,rfl⟩ := Option.map_eq_some_iff.mp hout
  apply slotWord (hi s hs)
  rcases facts.1 with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [wordAt,hs] using h)

theorem indexLookup_preserves (kinds : List IndexKind) (index : Nat) :
    Preserves Inv (indexLookup kinds index) := by
  rw [← indexLookupSource_eq]
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (MonadLift.monadLift a : WG.M α) :=
    hoare_liftAmbient a Inv
  have finish (entry : Option IndexEntry) : Preserves Inv (do
      if ← branch .idxFound entry.isSome then
        let some e := entry | invariant "unreachable"
        let peer ← Affiliation.acquireOwner e.owner
        if ← branch .idxPeerAlive peer.isSome then
          let some pid := peer | invariant "unreachable"
          return some (e.owner,pid)
      return none) := by
    apply preserves_bind (ambient (AmbientM.branch .idxFound entry.isSome))
    intro found
    cases found with
    | false => exact preserves_pure _
    | true =>
      cases entry with
      | none => exact preserves_bind (ambient (AmbientM.invariant "unreachable")) (fun _ => preserves_pure _)
      | some e =>
        apply preserves_bind (acquireOwner_preserves e.owner)
        intro peer
        apply preserves_bind (ambient (AmbientM.branch .idxPeerAlive peer.isSome))
        intro alive
        cases alive <;> cases peer
        all_goals first
          | exact preserves_pure _
          | exact preserves_bind (ambient (AmbientM.invariant "unreachable")) (fun _ => preserves_pure _)
  have indexFrame : Preserves Inv (liftIndex (indexBucket index)) := by
    apply hoare_liftIndex
    intro g d table hi hd
    apply fields_transport hi
    unfold fields Queues.RxCredits.keyWords
    rw [hd]
    rfl
  unfold indexLookupSource
  apply preserves_bind indexFrame
  intro entries
  refine hoare_bind _ _ (list_view_spec (id : WGWorld → WGWorld) Inv entries _ _ ?_) ?_
  · intro e acc
    apply preserves_bind (ambient (AmbientM.branch .idxWalk true))
    intro _
    apply preserves_bind (ambient (AmbientM.branch .idxMatch (e.index == index)))
    intro matched
    cases matched with
    | false => exact preserves_pure _
    | true =>
      apply preserves_bind (ambient (AmbientM.branch .idxTypeMatch (kinds.contains e.kind)))
      intro included
      cases included <;> exact preserves_pure _
  · rintro ⟨entry,stopped⟩
    cases stopped with
    | true => exact finish entry
    | false => exact preserves_bind (ambient (AmbientM.branch .idxWalk false)) (fun _ => finish entry)

theorem device_subset (hi : Inv w) (hd : w.dev = some d) (hv : v.dev = some after)
    (front : d.nextKeypairId ≤ after.nextKeypairId)
    (words : ∀ (kid : KeypairId) (key : Keypair), after.keypairs[kid]? = some key →
      ∃ old : Keypair, d.keypairs[kid]? = some old ∧ (key.peer = none ∨ key.peer = old.peer))
    (slots : ∀ (pid : PeerId) (p : Peer) (kid : KeypairId), after.peers[pid]? = some p →
      (p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid) →
      ∃ old : Peer, d.peers[pid]? = some old ∧
        (old.keypairCurrent = some kid ∨ old.keypairPrevious = some kid ∨ old.keypairNext = some kid)) :
    Inv v := by
  apply (inv_iff v).mpr
  intro out pid p kid ho hp hs
  have eq : out = after := Option.some.inj (ho.symm.trans hv)
  subst out
  obtain ⟨old,resident,selected⟩ := slots pid p kid hp hs
  have ref := (inv_iff w).mp hi d pid old kid hd resident selected
  refine ⟨Nat.lt_of_lt_of_le ref.1 front,?_⟩
  intro key hk
  obtain ⟨before,hb,word⟩ := words kid key hk
  exact (ref.2 before hb).reduce word

theorem peer_erase (hi : Inv w) (hd : w.dev = some d) (pid : PeerId) (dropped : Nat) :
    Inv {w with dev := some {d with peers := d.peers.erase pid,txDropped := dropped}} := by
  apply device_subset (after := {d with peers := d.peers.erase pid, txDropped := dropped}) hi hd rfl (Nat.le_refl _)
  · intro kid key hk
    exact ⟨key,hk,Or.inr rfl⟩
  · intro q p kid hp hs
    by_cases same : pid = q
    · simp [same] at hp
    · exact ⟨p,by simpa [Std.TreeMap.getElem?_erase,same] using hp,hs⟩

theorem peer_same (hi : Inv w) (hd : w.dev = some d) (hp : d.peers[pid]? = some old)
    (p : Peer) (same : slotCell p = slotCell old) :
    Inv {w with dev := some {d with peers := d.peers.insert pid p}} := by
  apply device_subset (after := {d with peers := d.peers.insert pid p}) hi hd rfl (Nat.le_refl _)
  · intro kid key hk
    exact ⟨key,hk,Or.inr rfl⟩
  · intro q peer kid hq hs
    by_cases selected : pid = q
    · subst q
      have eq : peer = p := by simpa using hq.symm
      subst peer
      refine ⟨old,hp,?_⟩
      have a := congrArg Prod.fst same
      have b := congrArg (fun t => t.2.1) same
      have c := congrArg (fun t => t.2.2) same
      dsimp only [slotCell] at a b c
      simpa only [a,b,c] using hs
    · exact ⟨peer,by simpa [Std.TreeMap.getElem?_insert,selected] using hq,hs⟩

theorem peerPut_preserves (peer : Option PeerId) : Preserves Inv (peerPut peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hi hr
  have hl (a : IndexM Unit) : (liftM a : WG.M Unit) = liftIndex a := rfl
  cases peer with
  | none =>
    simp [peerPut,branch,CounterWindow.branch_run,StateT.run_bind,
      StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind,
      CounterWindow.except_pure] at hr
    rcases hr with ⟨rfl,rfl⟩
    exact hi
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerPut,branch,CounterWindow.branch_run,requireNotPending,
        getPeer,getDev,hd,invariant,AmbientM.invariant,StateT.run_bind,
        StateT.run_monadLift,CounterWindow.except_ok_bind] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerPut,branch,CounterWindow.branch_run,requireNotPending,
          getPeer,getDev,hd,hp,invariant,AmbientM.invariant,StateT.run_bind,
          StateT.run_pure,StateT.run_monadLift,CounterWindow.except_ok_bind] at hr
        cases hr
      | some p =>
        by_cases zero : p.refcount = 0
        · simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
            CounterWindow.branchCmp_run,hd,hp,zero,StateT.run_bind,StateT.run_pure,
            StateT.run_monadLift,CounterWindow.except_ok_bind,CounterWindow.except_pure,
            unsupported,AmbientM.unsupported] at hr
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
          all_goals first
            | exact peer_same hi hd hp _ rfl
            | (apply fields_transport (peer_erase hi hd pid (d.txDropped + p.staged.length))
               unfold fields Queues.RxCredits.keyWords
               simp only [Option.map_some,Option.bind_some]
               refine Prod.ext rfl (Prod.ext ?_ rfl)
               funext q
               by_cases same : pid = q <;> simp [Std.TreeMap.getElem?_erase,Std.TreeMap.getElem?_insert,same])

private theorem fields_store {a : WG.M α} (ha : SameWGStore a) : SameView fields a :=
  ha.of_factor (fun k : WGStoreView => fields {dev := k.dev}) _ (fun _ => rfl)

private theorem fields_read (initial : _) (pid : PeerId) (f : Peer → WG.M α)
    (hf : ∀ p, initial.2.1 pid = some (slotCell p) →
      Preserves (fun w => fields w = initial) (f p)) :
    Preserves (fun w => fields w = initial) (getPeer pid >>= f) := by
  apply hoare_bind _ _ (show Hoare (getPeer pid) (fun w => fields w = initial)
    (fun p w => fields w = initial ∧ initial.2.1 pid = some (slotCell p)) from ?_)
  · intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi hr
    exact (hoare_iff_run_ambient _ _ _).mp (hf p hi.2) w a result v b hi.1 hr
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi hr
    obtain ⟨rfl,_,d,hd,hp⟩ := Queues.getPeer_normal pid w v p a b hr
    refine ⟨hi,?_⟩
    rw [←hi]
    simp [fields,hd,hp]

private theorem fields_set (initial : _) (pid : PeerId) (p : Peer)
    (hp : initial.2.1 pid = some (slotCell p)) :
    Preserves (fun w => fields w = initial) (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases hr
  apply Eq.trans _ hi
  cases hd : w.dev with
  | none =>
    rw [←hi] at hp
    simp [fields,hd] at hp
  | some d =>
    have saved : (d.peers[pid]?).map slotCell = some (slotCell p) := by
      rw [←hi] at hp
      simpa [fields,hd] using hp
    unfold fields Queues.RxCredits.keyWords
    simp only [hd,Option.map_some,Option.bind_some]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext q
    by_cases same : pid = q
    · subst q; simpa using saved.symm
    · simp [Std.TreeMap.getElem?_insert,same]

private theorem fields_modify (f : Device → Device)
    (front : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (peers : ∀ d, (f d).peers = d.peers)
    (keys : ∀ d, (f d).keypairs = d.keypairs) : SameView fields (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  cases hr
  unfold fields Queues.RxCredits.keyWords
  simp [Option.map_map,Option.bind_map,Function.comp_def,front,peers,keys]

macro "slot_fields_step " initial:term : tactic => `(tactic| first
  | (env_bind_head getPeer; apply fields_read $initial; intro p hp)
  | (rx_retention_head setPeer; apply fields_set $initial; assumption)
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a p v b hi hr
     simpa only [(Queues.getPeer_normal _ w v p a b hr).1] using hi)
  | (rx_retention_head liftSkb
     apply hoare_liftSkb
     intro w d store hi hd
     unfold fields Queues.RxCredits.keyWords at hi ⊢
     simpa only [hd,Option.map_some,Option.bind_some] using hi)
  | (rx_retention_head getDev; exact (fields_store getDev_sameWGStore).wp (fun s => s = $initial))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev
     apply (fields_modify _ ?_ ?_ ?_).wp (fun s => s = $initial)
     all_goals intro d; rfl)
  | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
  | rx_retention_step)

theorem dstCacheReset_fields (pid : PeerId) : SameView fields (dstCacheReset pid) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold dstCacheReset
  simp (config := {zeta := false}) only [hiddenJiffies,getAmbient]
  repeat' slot_fields_step initial

theorem resetLastSentHandshake_fields (pid : PeerId) : SameView fields (resetLastSentHandshake pid) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' slot_fields_step initial

theorem precomputeStaticStatic_fields (pid : PeerId) : SameView fields (precomputeStaticStatic pid) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold precomputeStaticStatic
  simp (config := {zeta := false}) only [requireNotPending,branch]
  repeat' slot_fields_step initial

theorem handshakeInit_fields (pid : PeerId) (psk : Option Key) : SameView fields (handshakeInit pid psk) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold handshakeInit IndexOwner.setPeerWord
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head precomputeStaticStatic; exact (precomputeStaticStatic_fields _).wp (fun s => s = initial))
    | slot_fields_step initial

theorem peerCreateCore_preserves (pid : PeerId) (key : Key) :
    Preserves Inv (Peers.peerCreateCore pid key) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  rw [Peers.peerCreateCore_run] at hr
  cases hr
  cases hd : w.dev with
  | none => simp [Inv,Affiliation.view,Peers.creationCoreWorld,hd]
  | some d =>
    apply device_subset (after := {d with nextPeer := pid + 1, peers := d.peers.insert pid (Peers.createdPeer key (w.peerCounter + 1))}) hi hd
      (by simp [Peers.creationCoreWorld,hd]) (Nat.le_refl _)
    · intro kid old hk
      exact ⟨old,hk,Or.inr rfl⟩
    · intro q p kid hp hs
      by_cases same : pid = q
      · subst q
        have eq : p = Peers.createdPeer key (w.peerCounter + 1) := by simpa using hp.symm
        simp [eq,Peers.createdPeer] at hs
      · exact ⟨p,by simpa [Std.TreeMap.getElem?_insert,same] using hp,hs⟩

/-- Creation replaces its chosen slot with the actual empty-slot peer. No
fresh-peer premise is needed for this invariant, even at an occupied frontier. -/
theorem peerCreate_preserves (key : Key) (psk : Option Key) : Preserves Inv (peerCreate key psk) := by
  rw [←Peers.peerCreateFactored_eq]
  unfold Peers.peerCreateFactored
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head Peers.peerCreateCore; exact peerCreateCore_preserves _ _)
    | (rx_retention_head dstCacheReset; exact fields_preserves (project := fun w => w) (dstCacheReset_fields _))
    | (rx_retention_head handshakeInit; exact fields_preserves (project := fun w => w) (handshakeInit_fields _ _))
    | (rx_retention_head resetLastSentHandshake; exact fields_preserves (project := fun w => w) (resetLastSentHandshake_fields _))
    | (rx_retention_head getDev; exact fields_preserves (project := fun w => w) (fields_store getDev_sameWGStore))
    | (rx_retention_head modifyDev; exact fields_preserves (project := fun w => w)
        (fields_modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step


theorem peerGet_fields (pid : PeerId) : SameView fields (peerGet pid) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold peerGet
  simp (config := {zeta := false}) only [requireNotPending,refcountInc,branchCmp,branch,unsupported]
  repeat' slot_fields_step initial

theorem publish_fields (id : SkbId) (state : PacketState) :
    SameView fields (Queues.RxWorkers.publishSource id state) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold Queues.RxWorkers.publishSource
  simp (config := {zeta := false}) only [getRxSkb,setRxSkb,invariant]
  repeat' first
    | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
    | (rx_retention_head peerGet; exact (peerGet_fields _).wp (fun s => s = initial))
    | slot_fields_step initial

theorem enqueuePerDeviceAndPeerRx_fields (id : SkbId) :
    SameView fields (enqueuePerDeviceAndPeerRx id) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold enqueuePerDeviceAndPeerRx
  simp (config := {zeta := false}) only [branch,setRxSkb,getRxSkb,queueDeviceWork]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom
       exact (fields_store (cpumaskNextOnlineFrom_sameStore _)).wp (fun s => s = initial))
    | slot_fields_step initial

/-- The native IRQ callback keeps its arbitrary action and explicit invariant
contract; no extra premise is imposed on the packet state being published. -/
theorem enqueuePerPeerRx_preserves (irq : WG.M Unit) (id : SkbId) (state : PacketState)
    (callback : Preserves Inv irq) : Preserves Inv (enqueuePerPeerRx irq id state) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  exact preserves_bind (fields_preserves (project := fun w => w) (publish_fields id state))
    (fun pid => preserves_bind callback (fun _ => peerPut_preserves (some pid)))

theorem keypairGet_preserves (kid : Option KeypairId) : Preserves Inv (keypairGet kid) := by
  apply view_preserves (project := fun w => w)
  intro initial
  exact hoare_consequence (Affiliation.keypairGet_affiliation kid initial)
    (fun _ h => h) (fun _ _ h => h.1)

theorem consumeData_preserves (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves Inv (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant,newRxSkb,freeRxSkb]
  repeat' first
    | (rx_retention_head indexLookup; exact indexLookup_preserves _ _)
    | (rx_retention_head keypairGet; exact keypairGet_preserves _)
    | (rx_retention_head keypairGetNull
       exact fields_preserves (project := fun w => w) (fields_store keypairGetNull_sameStore))
    | (rx_retention_head getPeer
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a p v b hi hr
       exact (Queues.getPeer_normal _ w v p a b hr).1 ▸ hi)
    | (rx_retention_head enqueuePerDeviceAndPeerRx
       exact fields_preserves (project := fun w => w) (enqueuePerDeviceAndPeerRx_fields _))
    | (rx_retention_head enqueuePerPeerRx
       exact enqueuePerPeerRx_preserves _ _ _ (preserves_pure _))
    | (rx_retention_head keypairPut; exact keypairPut_preserves _ _)
    | (rx_retention_head peerPut; exact peerPut_preserves _)
    | (rx_retention_head liftSkb
       apply hoare_liftSkb
       intro w d store hi hd
       apply fields_transport hi
       unfold fields Queues.RxCredits.keyWords
       simp only [hd,Option.map_some,Option.bind_some])
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ Inv)
    | rx_retention_step


/-- The product callback is unrestricted apart from preserving the same slot
invariant. Native publication and payment execute at their actual lift cuts. -/
theorem enqueuePerPeerRx_product (irq : Leanux.M Unit) (id : SkbId) (state : PacketState)
    (callback : Preserves (fun w : World => Inv w.wg) irq) :
    Preserves (fun w : World => Inv w.wg) (enqueuePerPeerRx irq id state) := by
  rw [Queues.RxWorkers.enqueue_source]
  apply preserves_bind (PublicationPoll.native_product Inv _
    (fields_preserves (project := fun w => w) (publish_fields id state)))
  intro pid
  exact preserves_bind callback (fun _ => PublicationPoll.native_product Inv _
    (peerPut_preserves (some pid)))

theorem packetReceive_preserves (msg : List UInt8) (src : SkbSource) :
    Preserves Inv (packetReceive msg src) := by
  unfold packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,queueDeviceWork,unsupported,invariant]
  repeat' first
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp Inv)
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp Inv)
    | (rx_retention_head consumeData; exact consumeData_preserves _ _ _)
    | (rx_retention_head getDev
       exact fields_preserves (project := fun w => w) (fields_store getDev_sameWGStore))
    | (rx_retention_head modifyDev
       apply fields_preserves (project := fun w => w)
       apply fields_modify
       all_goals intro d; rfl)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ Inv)
    | rx_retention_step

theorem wgReceive_preserves (msg : List UInt8) (src : SkbSource) :
    Preserves Inv (wgReceive msg src) := by
  unfold wgReceive
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head packetReceive; exact packetReceive_preserves _ _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ Inv)
    | rx_retention_step

end Leanux.Proofs.WG.CurrentSlots
