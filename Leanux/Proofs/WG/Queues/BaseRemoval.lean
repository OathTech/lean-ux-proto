import Leanux.Proofs.WG.Queues.DecryptCarrier
import Leanux.Proofs.WG.Queues.WorkReservations
import Leanux.Proofs.WG.Queues.JointDevice
import Leanux.Proofs.WG.Peers.ConfiguredAllowedIps

/-! Detaching a live-list entry does not pay its base reference. The stamped
owner moves to an explicit retained partition until actual final payment. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseRemoval
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

def view (w : WGWorld) := (DecryptCarrier.decryptView w,w.dev.map Device.peerList)

private theorem sameWG {α : Type} {a : WG.M α} (ha : SameWGStore a) : SameView view a :=
  ha.of_factor (fun s : WGStoreView => view {dev := s.dev}) _ (fun _ => rfl)

private theorem node_view {α : Type} {a : WG.M α} (ha : SameNode a) : SameView view a := by
  apply ha.of_factor (fun s : WGStoreView => view {dev := s.dev})
  intro w
  unfold view DecryptCarrier.decryptView carrierView stableView keyView
  unfold peerView rxView keyWords currentCells RxRing.nativeCell
  simp only [nodeView,wgStoreView,nodeDevice,Option.map_map,Option.bind_map,Function.comp_def]

private theorem unlisted_view (w : WGWorld) (d : Device) (hd : w.dev = some d) (id : NodeId) :
    view {w with dev := some (AllowedIps.unlisted d id)} = view w := by
  unfold view DecryptCarrier.decryptView carrierView stableView keyView
  unfold peerView rxView keyWords currentCells RxRing.nativeCell
  simp only [hd,Option.map_some,Option.bind_some,AllowedIps.unlisted_get,
    Option.map_map,Function.comp_def,AllowedIps.unlist]
  rfl

theorem listDel_view (id : NodeId) : SameView view (listDel id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  cases hd : w.dev with
  | none => simp [listDel,getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
  | some d =>
    obtain ⟨x,u,c,actual,_,state⟩ := (total_iff_run_ambient _ _ _).mp
      (AllowedIps.listDel_wp w d hd id) w a rfl
    cases actual.symm.trans hr
    rw [state]
    exact unlisted_view w d hd id

private theorem getPeer_view (pid : PeerId) : SameView view (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b hr
  exact congrArg view (getPeer_normal pid w v p a b hr).1

private theorem modifyDev_view (f : Device → Device)
    (hf : ∀ d, view {dev := some (f d)} = view {dev := some d}) : SameView view (modifyDev f) := by
  intro initial
  apply hoare_modify
  intro w h
  have same : view {w with dev := w.dev.map f} = view w := by
    unfold view DecryptCarrier.decryptView carrierView stableView keyView at hf ⊢
    unfold peerView rxView keyWords currentCells RxRing.nativeCell at hf ⊢
    cases hd : w.dev with
    | none => simp
    | some d => simpa only [hd,Option.map_some,Option.bind_some] using hf d
  exact same.trans h

theorem removeByPeer_view (pid : PeerId) : SameView view (removeByPeer pid) := by
  intro initial
  let P := fun w => view w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  change Preserves P _
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep
  apply preserves_bind ((getPeer_view pid).wp (fun s => s = initial))
  intro p
  apply preserves_bind (ambient (AmbientM.branch .removeListEmpty p.allowedipsList.isEmpty))
  intro empty
  cases empty with
  | true => exact preserves_pure ()
  | false =>
    apply preserves_bind ((modifyDev_view (fun d =>
      {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}})
      (fun _ => rfl)).wp (fun s => s = initial))
    intro _
    apply preserves_bind
    · apply list_view_spec view (fun s => s = initial)
      intro id acc
      change Preserves P (AllowedIps.removeStep id)
      unfold AllowedIps.removeStep
      apply preserves_bind (ambient (AmbientM.branch .removeListIter true))
      intro _
      apply preserves_bind ((listDel_view id).wp (fun s => s = initial))
      intro _
      exact (node_view (removeNodeBody_sameNode id)).wp (fun s => s = initial)
    · intro _
      exact preserves_bind (ambient (AmbientM.branch .removeListIter false))
        (fun _ => preserves_pure ())

private theorem mark_view (pid : PeerId) : SameView view (do
    let p ← getPeer pid
    setPeer pid {p with isDead := true}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,read,mid,hread,write⟩ := hr
  obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal pid w read p a mid hread
  cases write
  unfold view DecryptCarrier.decryptView carrierView stableView keyView
  unfold peerView rxView keyWords currentCells RxRing.nativeCell
  simp only [hd,Option.map_some,Option.bind_some]
  have credit : (fun q : PeerId => (d.peers.insert pid {p with isDead := true})[q]?.map
      (fun x : Peer => (x.internalId,x.refcount,x.rxQueue))) =
    (fun q : PeerId => d.peers[q]?.map (fun x : Peer => (x.internalId,x.refcount,x.rxQueue))) := by
    funext q
    by_cases eq : pid = q <;> simp_all [Std.TreeMap.getElem?_insert]
  have current : (fun q : PeerId => (d.peers.insert pid {p with isDead := true})[q]?.map currentCell) =
    (fun q : PeerId => d.peers[q]?.map currentCell) := by
    funext q
    by_cases eq : pid = q <;> simp_all [Std.TreeMap.getElem?_insert,currentCell]
  have cold : (fun q : PeerId => (d.peers.insert pid {p with isDead := true})[q]?.map
      (fun x : Peer => (x.rxQueue,x.napiScheduled))) =
    (fun q : PeerId => d.peers[q]?.map (fun x : Peer => (x.rxQueue,x.napiScheduled))) := by
    funext q
    by_cases eq : pid = q <;> simp_all [Std.TreeMap.getElem?_insert]
  rw [credit,current,cold]

private theorem afterUnlist_view (pid : PeerId) : SameView view (do
    removeByPeer pid
    _ ← branch .pubkeyRemoveHashed ((← getDev).peerHashtable.any (·.2 == pid))
    modifyDev fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}
    let p ← getPeer pid
    setPeer pid {p with isDead := true}) := by
  intro initial
  let P := fun w => view w = initial
  change Preserves P _
  apply preserves_bind ((removeByPeer_view pid).wp (fun s => s = initial))
  intro _
  apply preserves_bind ((sameWG getDev_sameWGStore).wp (fun s => s = initial))
  intro d
  apply preserves_bind (hoare_liftAmbient
    (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid))) P)
  intro _
  apply preserves_bind ((modifyDev_view
    (fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)})
    (fun _ => rfl)).wp (fun s => s = initial))
  intro _
  exact (mark_view pid).wp (fun s => s = initial)

theorem peerMakeDead_normal (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (hr : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) :
    DecryptCarrier.decryptView v = DecryptCarrier.decryptView w ∧
      v.dev.map Device.peerList = (w.dev.map Device.peerList).map (List.filter (· != pid)) := by
  unfold peerMakeDead at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,middle,ambient,unlist,rest⟩ := hr
  cases unlist
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (afterUnlist_view pid) _ a () v b rest
  unfold view at frame
  constructor
  · refine (congrArg Prod.fst frame).trans ?_
    unfold DecryptCarrier.decryptView carrierView stableView keyView
    unfold peerView rxView keyWords currentCells RxRing.nativeCell
    cases hd : w.dev <;> simp [hd]
  · simpa only [Option.map_map,Function.comp_def] using congrArg Prod.snd frame

theorem peerMakeDead_preserves (pid : PeerId) :
    Preserves (fun w => CarrierState cs loans w ∧ StableRx cs w) (peerMakeDead pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases result
  have frame := (peerMakeDead_normal pid w v a b hr).1
  exact ⟨hi.1.view (congrArg Prod.fst frame),hi.2.view (congrArg Prod.snd frame)⟩

/-- Every matching occurrence is detached; no owner is released by filtering. -/
def live (owners : Reservations) (pid : PeerId) : Reservations :=
  owners.filter (fun o => o.slot != pid)

def detached (owners : Reservations) (pid : PeerId) : Reservations :=
  owners.filter (fun o => o.slot == pid)

theorem partition (owners : Reservations) (pid : PeerId) :
    owners.Perm (live owners pid ++ detached owners pid) := by
  simpa only [live,detached,bne_eq,Bool.not_not] using (List.filter_append_perm (fun o : Owner => o.slot != pid) owners).symm

theorem live_slots (owners : Reservations) (pid : PeerId) :
    (live owners pid).map Owner.slot = (owners.map Owner.slot).filter (· != pid) := by
  simpa only [live,Function.comp_def] using
    (List.filter_map (f := Owner.slot) (p := (· != pid)) (l := owners)).symm

theorem detached_member (member : o ∈ owners) (slot : o.slot = pid) :
    o ∈ detached owners pid := by
  simp [detached,member,slot]

theorem peerMakeDead_accounts (pid : PeerId)
    (hi : CarrierState cs (owners ++ loans) w) (hs : StableRx cs w)
    (listed : w.dev.map Device.peerList = some (owners.map Owner.slot))
    (a b : Ambient) (hr : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) :
    CarrierState cs (live owners pid ++ (detached owners pid ++ loans)) v ∧
      StableRx cs v ∧ v.dev.map Device.peerList = some ((live owners pid).map Owner.slot) := by
  have normal := peerMakeDead_normal pid w v a b hr
  have carried := hi.view (congrArg Prod.fst normal.1)
  refine ⟨WorkReservations.carrier_loans_perm carried ?_,
    hs.view (congrArg Prod.snd normal.1),?_⟩
  · simpa only [List.append_assoc] using (partition owners pid).append_right loans
  · rw [normal.2,listed,Option.map_some,live_slots]

theorem rootRemovePeerLists_view (root : NodeId) :
    SameView view (rootRemovePeerLists root) := by
  intro initial
  let P := fun w : WGWorld => view w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have device : Preserves P getDev := by
    unfold getDev
    apply preserves_bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact preserves_pure d
  have peer (pid : PeerId) : Preserves P (getPeer pid) :=
    (getPeer_view pid).wp (fun s => s = initial)
  have aip {α : Type} (a : AipM α) : Preserves P (liftAip a) := by
    apply hoare_liftAip a P
    intro w d store hi hd
    unfold P view DecryptCarrier.decryptView carrierView stableView keyView at hi ⊢
    unfold peerView rxView keyWords currentCells RxRing.nativeCell at hi ⊢
    simpa only [hd,Option.map_some,Option.bind_some] using hi
  have children (cs : List (Option NodeId)) (stack : List NodeId) :
      Preserves P (AllowedIps.pushChildren cs stack) := by
    unfold AllowedIps.pushChildren
    apply list_view_spec view (fun s => s = initial)
    intro c rest
    unfold AllowedIps.pushChild
    apply preserves_bind (ambient (AmbientM.branch .pushRcuNonNull c.isSome))
    intro nonnull
    cases nonnull <;> cases c <;> exact preserves_pure _
  have step (i : Nat) (stack : Option Unit × List NodeId) :
      Preserves P (AllowedIps.rootRemoveStep i stack) := by
    unfold AllowedIps.rootRemoveStep
    cases stack.2 with
    | nil =>
      exact preserves_bind (ambient (AmbientM.branch .rootRemoveLenPositive false))
        (fun _ => preserves_pure _)
    | cons id rest =>
      apply preserves_bind (ambient (AmbientM.branch .rootRemoveLenPositive true))
      intro _
      apply preserves_bind (ambient (AmbientM.branch .rootRemovePopped true))
      intro _
      apply preserves_bind (aip (getNode id))
      intro n
      apply preserves_bind (children n.bit.toList rest)
      intro next
      apply preserves_bind (ambient (AmbientM.branch .rootRemoveHasPeer n.peer.isSome))
      intro hasPeer
      cases hasPeer with
      | false => exact preserves_pure _
      | true =>
        cases n.peer with
        | none =>
          exact preserves_bind (ambient (AmbientM.invariant "unreachable"))
            (fun _ => preserves_pure _)
        | some pid =>
          apply preserves_bind (peer pid)
          intro p
          split
          · exact preserves_bind (ambient (AmbientM.invariant "trie node missing from its peer's list"))
              (fun _ => preserves_bind ((listDel_view id).wp (fun s => s = initial))
                (fun _ => preserves_pure _))
          · exact preserves_bind ((listDel_view id).wp (fun s => s = initial))
              (fun _ => preserves_pure _)
  rw [← AllowedIps.rootRemoveSource_eq]
  unfold AllowedIps.rootRemoveSource
  apply preserves_bind device
  intro d
  apply preserves_bind
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    exact list_view_spec view (fun s => s = initial) _ _ _ step
  · intro result
    cases result.1 with
    | none => exact ambient (AmbientM.invariant "root_remove_peer_lists did not terminate")
    | some x => exact preserves_pure x

theorem allowedipsFree_view : SameView view WG.free := by
  intro initial
  let P := fun w : WGWorld => view w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have device : Preserves P getDev := by
    unfold getDev
    apply preserves_bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact preserves_pure d
  have aip {α : Type} (a : AipM α) : Preserves P (liftAip a) := by
    apply hoare_liftAip a P
    intro w d store hi hd
    unfold P view DecryptCarrier.decryptView carrierView stableView keyView at hi ⊢
    unfold peerView rxView keyWords currentCells RxRing.nativeCell at hi ⊢
    simpa only [hd,Option.map_some,Option.bind_some] using hi
  unfold WG.free
  apply preserves_bind device
  intro d
  apply preserves_bind ((modifyDev_view
    (fun q => {q with peerAllowedips := {root4 := none, root6 := none, seq := d.peerAllowedips.seq + 1}})
    (fun _ => rfl)).wp (fun s => s = initial))
  intro _
  apply preserves_bind
  · apply list_view_spec view (fun s => s = initial)
    intro item acc
    rcases item with ⟨old, decision⟩
    apply preserves_bind (ambient (AmbientM.branch decision old.isSome))
    intro present
    cases present with
    | false => exact preserves_pure _
    | true =>
      cases old with
      | none => exact preserves_pure _
      | some root =>
        apply preserves_bind ((rootRemovePeerLists_view root).wp (fun s => s = initial))
        intro _
        apply preserves_bind (aip (subtree root))
        intro nodes
        apply preserves_bind
        · apply list_view_spec view (fun s => s = initial)
          intro id _
          exact preserves_bind (aip (freeNode id)) (fun _ => preserves_pure _)
        · intro _
          exact preserves_pure _
  · intro _
    exact preserves_pure _


/-- The existing bulk-removal prefix clears the trie before saving its list. -/
def entry : WG.M (List PeerId) := do
  WG.free
  return (← getDev).peerList

theorem peerRemoveAll_entry : peerRemoveAll = (do
    let dead ← entry
    for pid in dead do
      _ ← branch .peerRemoveAllIter1 true
      peerMakeDead pid
    _ ← branch .peerRemoveAllIter1 false
    for pid in dead do
      _ ← branch .peerRemoveAllIter2 true
      peerRemoveAfterDead pid
    _ ← branch .peerRemoveAllIter2 false
    pure ()) := by
  simp only [Configuration.peerRemoveAll_factor,Configuration.peerRemoveAllWith,entry,
    bind_assoc,pure_bind]

theorem entry_normal (hi : CarrierState cs (owners ++ loans) w) (hs : StableRx cs w)
    (listed : w.dev.map Device.peerList = some (owners.map Owner.slot))
    (a b : Ambient) (hr : (entry.run w).run a = .ok ((dead,v),b)) :
    dead = owners.map Owner.slot ∧ CarrierState cs (owners ++ loans) v ∧
      StableRx cs v ∧ v.dev.map Device.peerList = some dead := by
  unfold entry at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,mid,ambient,hfree,rest⟩ := hr
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp allowedipsFree_view w a u mid ambient hfree
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨d,read,c,hread,finish⟩ := rest
  obtain ⟨readEq,timeEq,hd⟩ := DecryptCarrier.getDev_current ambient c hread
  subst read
  subst c
  have final : (d.peerList = dead ∧ mid = v) ∧ ambient = b := by simpa using finish
  obtain ⟨⟨result,state⟩,time⟩ := final
  subst dead
  subst v
  subst b
  have listFrame := congrArg Prod.snd frame
  change mid.dev.map Device.peerList = w.dev.map Device.peerList at listFrame
  have same : d.peerList = owners.map Owner.slot := by
    rw [hd,Option.map_some,listed] at listFrame
    exact Option.some.inj listFrame
  have credit := congrArg Prod.fst frame
  change DecryptCarrier.decryptView mid = DecryptCarrier.decryptView w at credit
  exact ⟨same,hi.view (congrArg Prod.fst credit),hs.view (congrArg Prod.snd credit),by simp [hd]⟩

end Leanux.Proofs.WG.Queues.RxCredits.BaseRemoval
