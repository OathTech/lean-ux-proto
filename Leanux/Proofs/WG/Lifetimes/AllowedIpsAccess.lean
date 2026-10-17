import Leanux.Proofs.WG.Lifetimes.SavedPeers
import Leanux.Proofs.Logged.PrefixBatch
import Leanux.Proofs.Framing.WGAllowedIps

/-! Complete local allowed-IP list/removal calls. The saved peer-map walk logs
one read for every tested entry and each hit's saved-value write in source order.
Node-only walks retain their original failures and finite exhaustion bounds. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem nodeView_identity_metadata (w v : WGWorld)
    (he : nodeView v = nodeView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  let observe : WGStoreView → IdentityView × AllocationMetadata := fun s =>
    ((⟨s.peerCounter, fun i => (s.dev.bind fun d => d.peers[i]?).map (·.internalId)⟩,
      (fun i => (s.dev.bind fun d => d.keypairs[i]?).map (·.internalId)),
      fun slot => s.dev.bind fun d => match slot with
        | .inl i => d.txSkbs[i]?.map (fun _ => (d.ifindex, i + 1))
        | .inr i => d.rxSkbs[i]?.map (fun _ => (d.ifindex, i + 1))),
      ⟨s.keypairCounter, s.netIfindexNext, s.dev.map deviceAllocationMetadata⟩)
  have factor (g : WGWorld) : observe (nodeView g) = (identityView g, allocationMetadata g) := by
    unfold identityView keypairResidents packetResidents allocationMetadata
    cases hg : g.dev <;>
      simp [observe, nodeView, wgStoreView, nodeDevice, Peers.snapshot,
        deviceAllocationMetadata, hg]
    all_goals rfl
  simpa only [factor] using congrArg observe he

def NodeStable (I : List LifetimeEvent → WGWorld → Prop) : Prop :=
  ∀ h w v, nodeView v = nodeView w → I h w → I h v

/-- The original product observation keeps every other store field. -/
def productNodeView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter), nodeView w.wg)

def ProductNodeStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, productNodeView v = productNodeView w → I h w → I h v

theorem allocationNodeStable : NodeStable AllocationInv := by
  intro h w v he hi
  have hf := nodeView_identity_metadata w v he
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem nodeLift_spec (c : AmbientContracts I) (hc : NodeStable I)
    (P : IdentityView → Prop) (a : WG.M α) (ha : SameNode a) :
    AmbientSpec I P (liftWGPrefix a) (fun _ => P) := by
  apply StatePrefixEnsures.lift a (fun h w _ hi => c.safe h w hi.1)
  intro h w ambient x v ambient' hi hr
  have hf := (ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr
  refine ⟨hc h w v hf hi.1, ?_⟩
  have hid : identityView v = identityView w := congrArg Prod.fst (nodeView_identity_metadata w v hf)
  change P (identityView v)
  rw [hid]
  exact hi.2

/-- The original arbitrary product action is retained at its actual state type. -/
theorem nodeLift_spec_product (c : ProductAmbientContracts I) (hc : ProductNodeStable I)
    (P : IdentityView → Prop) (a : Leanux.M α) (ha : SameView productNodeView a) :
    ProductAmbientSpec I P (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a (fun h w hi => c.safe h w hi.1)
  intro h w x v hi hr
  have hf := (ProjectedAction.iff_run _ _ _).mp ha w x v hr
  refine ⟨hc h w v hf hi.1, ?_⟩
  have hid : identityView v.wg = identityView w.wg := congrArg Prod.fst (nodeView_identity_metadata w.wg v.wg
    (congrArg (fun s : ProductStore43 => s.2.2.2) hf))
  change P (identityView v.wg)
  rw [hid]
  exact hi.2

private theorem nodeLift_native_product (c : ProductAmbientContracts I) (hc : ProductNodeStable I)
    (P : IdentityView → Prop) (a : WG.M α) (ha : SameNode a) :
    ProductAmbientSpec I P (liftWGObserver (liftWGPrefix a)) (fun _ => P) := by
  rw [liftWGObserver_lift]
  apply nodeLift_spec_product c hc P
  exact sameView_liftWG productNodeView nodeView a ha (fun w g ambient he => by
    simp only [productNodeView, he])

private theorem allowed_readAip {a : AipM α} (ha : SameView (fun s : AipStore => s) a) :
    SameWGStore (liftAip a) := by
  intro initial
  apply hoare_liftAip_of a (fun w => wgStoreView w = initial) (fun _ w => wgStoreView w = initial)
  intro g d hg hd
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro s ambient x s' ambient' hs hr
  have he := (ProjectedAction.iff_run_ambient _ _ _).mp ha s ambient x s' ambient' hr
  rw [he, hs]
  simpa [wgStoreView, hd] using hg

private theorem allowed_getDev : SameWGStore getDev := by
  intro initial
  unfold Hoare
  mvcgen [getDev, invariant, AmbientM.invariant]

private theorem allowed_erase_bind_pure {g : MixedM α} {x : α}
    {f : α → MixedM β} {a : WG.M β}
    (hg : ErasesStatePrefix g (pure x)) (hf : ErasesStatePrefix (f x) a) :
    ErasesStatePrefix (g >>= f) a := by
  intro w
  change ErasesPrefix ((g.run w) >>= fun out => (f out.1).run out.2) (a.run w)
  exact erasesPrefix_bind_pure (x := (x, w)) (hg w) (hf w)

private theorem allowed_erase_ite (p : Prop) [Decidable p]
    {g h : MixedM α} {a b : WG.M α}
    (hg : p → ErasesStatePrefix g a) (hh : ¬p → ErasesStatePrefix h b) :
    ErasesStatePrefix (if p then g else h) (if p then a else b) := by
  split <;> simp_all

private theorem allowed_state_ite {I : List LifetimeEvent → WGWorld → Prop} (p : Prop) [Decidable p] {a b : MixedM α}
    (ha : p → StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe a)
    (hb : ¬p → StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe b) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (if p then a else b) := by
  split <;> simp_all

private theorem allowed_lift_forIn (xs : List α) (init : β)
    (f : α → β → MixedM (ForInStep β)) :
    liftWGObserver (forIn xs init f) = forIn xs init (fun x b => liftWGObserver (f x b)) := by
  induction xs generalizing init with
  | nil => simp only [List.forIn_nil, liftWGObserver_pure]
  | cons x xs ih =>
    simp only [List.forIn_cons, liftWGObserver_bind]
    congr 1
    funext step
    cases step with
    | done b => exact liftWGObserver_pure b
    | yield b => exact ih b

def listAddTailPrefix (pid : PeerId) (id : NodeId) : MixedM Unit := do
  let p ← getPeerMixed pid
  setPeerMixed pid {p with allowedipsList := p.allowedipsList ++ [id]}

def listDelEntriesPrefix (id : NodeId) : List (PeerId × Peer) → MixedM Unit
  | [] => pure ()
  | (pid,p) :: rest => do
    savedPeerRead pid p
    if p.allowedipsList.contains id then
      setPeerMixed pid {p with allowedipsList := listRemove p.allowedipsList id}
    listDelEntriesPrefix id rest

def listDelPrefix (id : NodeId) : MixedM Unit := do
  let d ← liftWGPrefix getDev
  listDelEntriesPrefix id d.peers.toList

theorem listAddTailPrefix_erases (pid : PeerId) (id : NodeId) :
    ErasesStatePrefix (listAddTailPrefix pid id) (listAddTail pid id) :=
  erasesStatePrefix_bind (getPeerMixed_erases pid) (fun _ => setPeerMixed_erases _ _)

theorem listDelEntriesPrefix_erases (id : NodeId) (xs : List (PeerId × Peer)) :
    ErasesStatePrefix (listDelEntriesPrefix id xs) (do
      for (pid,p) in xs do
        if p.allowedipsList.contains id then
          setPeer pid {p with allowedipsList := listRemove p.allowedipsList id}) := by
  induction xs with
  | nil => exact erasesStatePrefix_pure _
  | cons x xs ih =>
    rcases x with ⟨pid,p⟩
    simp only [List.forIn_cons]
    unfold listDelEntriesPrefix
    apply allowed_erase_bind_pure (erasesStatePrefix_emit _)
    cases ht : p.allowedipsList.contains id <;>
      simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
    · exact ih
    · exact erasesStatePrefix_bind (setPeerMixed_erases pid _) (fun _ => ih)

theorem listDelPrefix_erases (id : NodeId) : ErasesStatePrefix (listDelPrefix id) (listDel id) :=
  erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun d => listDelEntriesPrefix_erases id d.peers.toList)

theorem listAddTailPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (id : NodeId) : AmbientSpec I P (listAddTailPrefix pid id) (fun _ => P) :=
  StatePrefixEnsures.bind (c.getPeer P pid) (fun p => c.setPeer P pid {p with allowedipsList := p.allowedipsList ++ [id]})

theorem listDelEntriesPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (id : NodeId) (xs : List (PeerId × Peer)) :
    AmbientSpec I (fun s => P s ∧ SavedPeers xs s) (listDelEntriesPrefix id xs) (fun _ => P) := by
  induction xs with
  | nil =>
    exact (c.pure (fun s => P s ∧ SavedPeers [] s) ()).consequence
      (fun _ _ _ hi => hi) (fun _ _ _ _ hi => ⟨hi.1, hi.2.1⟩)
  | cons x xs ih =>
    rcases x with ⟨pid,p⟩
    unfold listDelEntriesPrefix
    have hread : AmbientSpec I (fun s => P s ∧ SavedPeers ((pid,p)::xs) s)
        (savedPeerRead pid p) (fun _ s => (P s ∧ SavedPeers xs s) ∧ s.1.slots pid = some p.internalId) :=
      (savedPeerRead_spec c (fun s => P s ∧ SavedPeers xs s) pid p).consequence
      (fun _ _ _ hi => ⟨hi.1, ⟨hi.2.1, fun i q hq => hi.2.2 i q (by simp [hq])⟩,
        hi.2.2 pid p (by simp)⟩) (fun _ _ _ _ hi => hi)
    apply StatePrefixEnsures.bind hread
    intro _
    split
    · exact StatePrefixEnsures.bind
        (c.setPeer (fun s => P s ∧ SavedPeers xs s) pid
          {p with allowedipsList := listRemove p.allowedipsList id}) (fun _ => ih)
    · exact ih.consequence (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩) (fun _ _ _ _ hi => hi)

theorem listDelPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (id : NodeId) :
    AmbientSpec I P (listDelPrefix id) (fun _ => P) :=
  StatePrefixEnsures.bind (getDev_saved_spec c P) (fun d => listDelEntriesPrefix_spec c P id d.peers.toList)

theorem listAddTailPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (id : NodeId) : ProductAmbientSpec I P (liftWGObserver (listAddTailPrefix pid id)) (fun _ => P) := by
  simp only [listAddTailPrefix, liftWGObserver_bind]
  exact PrefixEnsures.bind (c.getPeer P pid) (fun p => c.setPeer P pid {p with allowedipsList := p.allowedipsList ++ [id]})

theorem listDelEntriesPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (id : NodeId) (xs : List (PeerId × Peer)) :
    ProductAmbientSpec I (fun s => P s ∧ SavedPeers xs s) (liftWGObserver (listDelEntriesPrefix id xs)) (fun _ => P) := by
  induction xs with
  | nil =>
    simpa only [listDelEntriesPrefix, liftWGObserver_pure] using (c.pure (fun s => P s ∧ SavedPeers [] s) ()).consequence
      (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
  | cons x xs ih =>
    rcases x with ⟨pid,p⟩
    simp only [listDelEntriesPrefix, liftWGObserver_bind, apply_ite]
    have hread : ProductAmbientSpec I (fun s => P s ∧ SavedPeers ((pid,p)::xs) s)
        (liftWGObserver (savedPeerRead pid p)) (fun _ s => (P s ∧ SavedPeers xs s) ∧ s.1.slots pid = some p.internalId) :=
      (savedPeerRead_spec_product c (fun s => P s ∧ SavedPeers xs s) pid p).consequence
      (fun _ _ hi => ⟨hi.1, ⟨hi.2.1, fun i q hq => hi.2.2 i q (by simp [hq])⟩,
        hi.2.2 pid p (by simp)⟩) (fun _ _ _ hi => hi)
    apply PrefixEnsures.bind hread
    intro _
    split
    · exact PrefixEnsures.bind
        (c.setPeer (fun s => P s ∧ SavedPeers xs s) pid
          {p with allowedipsList := listRemove p.allowedipsList id}) (fun _ => ih)
    · exact ih.consequence (fun _ _ hi => ⟨hi.1, hi.2.1⟩) (fun _ _ _ hi => hi)

theorem listDelPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop) (id : NodeId) :
    ProductAmbientSpec I P (liftWGObserver (listDelPrefix id)) (fun _ => P) := by
  simp only [listDelPrefix, liftWGObserver_bind]
  exact PrefixEnsures.bind (getDev_saved_spec_product c P) (fun d => listDelEntriesPrefix_spec_product c P id d.peers.toList)

def removeByPeerPrefix (pid : PeerId) : MixedM Unit := do
  let p ← getPeerMixed pid
  if ← liftWGPrefix (branch .removeListEmpty p.allowedipsList.isEmpty) then return
  liftWGPrefix (modifyDev fun d => {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}})
  let _ ← forIn p.allowedipsList () (fun id _ => do
    _ ← liftWGPrefix (branch .removeListIter true)
    listDelPrefix id
    liftWGPrefix (AllowedIps.removeNodeBody id))
  _ ← liftWGPrefix (branch .removeListIter false)

def rootRemovePeerListsPrefix (root : NodeId) : MixedM Unit := do
  let mut stack := [root]
  for _ in [0:(← liftWGPrefix getDev).nodes.size + 1] do
    match stack with
    | [] => do _ ← liftWGPrefix (branch .rootRemoveLenPositive false); return
    | id :: rest =>
      _ ← liftWGPrefix (branch .rootRemoveLenPositive true)
      _ ← liftWGPrefix (branch .rootRemovePopped true)
      stack := rest
      let n ← liftWGPrefix (liftAip (getNode id))
      for c in n.bit.toList do
        if ← liftWGPrefix (branch .pushRcuNonNull c.isSome) then
          if let some c := c then stack := c :: stack
      if ← liftWGPrefix (branch .rootRemoveHasPeer n.peer.isSome) then
        let some pid := n.peer | liftWGPrefix (invariant "unreachable")
        if !(← getPeerMixed pid).allowedipsList.contains id then
          liftWGPrefix (invariant "trie node missing from its peer's list")
        listDelPrefix id
  liftWGPrefix (invariant "root_remove_peer_lists did not terminate")

def freeAllowedIpsPrefix : MixedM Unit := do
  let t := (← liftWGPrefix getDev).peerAllowedips
  liftWGPrefix (modifyDev fun d => {d with peerAllowedips := {root4 := none, root6 := none, seq := t.seq + 1}})
  for (old, d) in [(t.root4, Decision.freeHasRoot4), (t.root6, Decision.freeHasRoot6)] do
    if ← liftWGPrefix (branch d old.isSome) then
      if let some root := old then
        rootRemovePeerListsPrefix root
        for id in ← liftWGPrefix (liftAip (subtree root)) do liftWGPrefix (liftAip (freeNode id))

def deadPeerList (pid : PeerId) (d : Device) : Device :=
  {d with peerList := d.peerList.filter (· != pid)}
def deadPeerHashtable (pid : PeerId) (d : Device) : Device :=
  {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}

def peerMakeDeadPrefix (pid : PeerId) : MixedM Unit := do
  liftWGPrefix (modifyDev (deadPeerList pid))
  removeByPeerPrefix pid
  _ ← liftWGPrefix (branch .pubkeyRemoveHashed ((← liftWGPrefix getDev).peerHashtable.any (·.2 == pid)))
  liftWGPrefix (modifyDev (deadPeerHashtable pid))
  modifyPeerKeysPrefix pid fun p => {p with isDead := true}

theorem removeByPeerPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (removeByPeerPrefix pid) (removeByPeer pid) := by
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold removeByPeerPrefix AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp only [liftWGPrefix]
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact listDelPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply allowed_erase_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem rootRemovePeerListsPrefix_erases (root : NodeId) :
    ErasesStatePrefix (rootRemovePeerListsPrefix root) (rootRemovePeerLists root) := by
  unfold rootRemovePeerListsPrefix rootRemovePeerLists
  simp only [liftWGPrefix, Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact listDelPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply allowed_erase_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

  all_goals try simp_all only [List.cons.injEq, Option.some.injEq, reduceCtorEq, forall_eq']
  all_goals subst_vars
  all_goals repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact listDelPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply allowed_erase_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals try simp_all

theorem freeAllowedIpsPrefix_erases : ErasesStatePrefix freeAllowedIpsPrefix free := by
  unfold freeAllowedIpsPrefix free
  simp only [liftWGPrefix]
  repeat' first
    | with_reducible exact rootRemovePeerListsPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply allowed_erase_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

  all_goals try simp_all only [Option.some.injEq, forall_eq']
  all_goals subst_vars
  all_goals first | exact rootRemovePeerListsPrefix_erases _ | exact erasesStatePrefix_lift _ | exact erasesStatePrefix_pure _

theorem peerMakeDeadPrefix_erases (pid : PeerId) : ErasesStatePrefix (peerMakeDeadPrefix pid) (peerMakeDead pid) := by
  unfold peerMakeDeadPrefix peerMakeDead modifyPeerKeysPrefix
  simp only [liftWGPrefix]
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  apply erasesStatePrefix_bind (removeByPeerPrefix_erases pid)
  intro _
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro d
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  exact erasesStatePrefix_bind (getPeerMixed_erases pid) (fun _ => setPeerMixed_erases _ _)


/-- Scalar peer-list/hash bookkeeping is separate from the node-only mask. -/
structure AllowedIpsContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  nodes : NodeStable I
  peerList : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (modifyDev (deadPeerList pid)))
  peerHashtable : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (modifyDev (deadPeerHashtable pid)))

theorem allocationAllowedIps : AllowedIpsContracts AllocationInv := by
  constructor
  · exact allocationNodeStable
  all_goals
    intro pid
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [deadPeerList, deadPeerHashtable, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, deadPeerList,
        deadPeerHashtable, Option.map_map, Function.comp_def] <;> rfl

theorem nodeModify_preserves (c : AmbientContracts I) (hc : NodeStable I)
    (f : Device → Device) (hf : ∀ d, nodeDevice (f d) = nodeDevice d) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (modifyDev f)) :=
  AmbientContracts.drop (nodeLift_spec c hc (fun _ => True) _
    (by apply SameView.of_wp; intro initial; exact modifyDev_node_spec (fun s => s = initial) f hf))

structure ProductAllowedIpsContracts (I : List LifetimeEvent → World → Prop) : Prop where
  nodes : ProductNodeStable I
  peerList : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev (deadPeerList pid))))
  peerHashtable : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev (deadPeerHashtable pid))))

theorem nodeModify_preserves_product (c : ProductAmbientContracts I) (hc : ProductNodeStable I)
    (f : Device → Device) (hf : ∀ d, nodeDevice (f d) = nodeDevice d) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (modifyDev f))) :=
  ProductAmbientContracts.drop (nodeLift_native_product c hc (fun _ => True) _
    (by apply SameView.of_wp; intro initial; exact modifyDev_node_spec (fun s => s = initial) f hf))

theorem removeByPeerPrefix_preserves (c : AmbientContracts I) (hc : NodeStable I) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (removeByPeerPrefix pid) := by
  unfold removeByPeerPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (listDelPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (nodeLift_spec c hc (fun _ => True) _ (removeNodeBody_sameNode _))
    | with_reducible exact nodeModify_preserves c hc _ (fun _ => rfl)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | exact StatePrefixEnsures.pure _ (fun h w (_ : Ambient) hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | exact fun _ h w (_ : Ambient) hi => c.safe h w hi
    | with_reducible apply StatePrefixEnsures.forInInvariant (I := fun _ h w (_ : Ambient) => I h w)
    | with_reducible apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => I h w)
    | with_reducible apply allowed_state_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem rootRemovePeerListsPrefix_preserves (c : AmbientContracts I) (root : NodeId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (rootRemovePeerListsPrefix root) := by
  unfold rootRemovePeerListsPrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (listDelPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.store (fun _ => True) _ allowed_getDev)
    | with_reducible exact AmbientContracts.drop (c.store (fun _ => True) _ (allowed_readAip (getNode_sameAipStore _)))
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | exact StatePrefixEnsures.pure _ (fun h w (_ : Ambient) hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | exact fun _ h w (_ : Ambient) hi => c.safe h w hi
    | with_reducible apply StatePrefixEnsures.forInInvariant (I := fun _ h w (_ : Ambient) => I h w)
    | with_reducible apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => I h w)
    | with_reducible apply allowed_state_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem freeAllowedIpsPrefix_preserves (c : AmbientContracts I) (hc : NodeStable I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe freeAllowedIpsPrefix := by
  unfold freeAllowedIpsPrefix
  repeat' first
    | with_reducible exact rootRemovePeerListsPrefix_preserves c _
    | with_reducible exact AmbientContracts.drop (c.store (fun _ => True) _ allowed_getDev)
    | with_reducible exact AmbientContracts.drop (c.store (fun _ => True) _ (allowed_readAip (subtree_sameAipStore _)))
    | with_reducible exact AmbientContracts.drop (nodeLift_spec c hc (fun _ => True) _ (liftAip_sameNode (freeNode_sameNextNode _)))
    | with_reducible exact nodeModify_preserves c hc _ (fun _ => rfl)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | exact StatePrefixEnsures.pure _ (fun h w (_ : Ambient) hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | exact fun _ h w (_ : Ambient) hi => c.safe h w hi
    | with_reducible apply StatePrefixEnsures.forInInvariant (I := fun _ h w (_ : Ambient) => I h w)
    | with_reducible apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => I h w)
    | with_reducible apply allowed_state_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem peerMakeDeadPrefix_preserves (c : AmbientContracts I) (r : AllowedIpsContracts I) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (peerMakeDeadPrefix pid) := by
  unfold peerMakeDeadPrefix
  apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => I h w) (r.peerList pid)
  intro _
  apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => I h w) (removeByPeerPrefix_preserves c r.nodes pid)
  intro _
  apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => I h w) (AmbientContracts.drop (c.store (fun _ => True) _ allowed_getDev))
  intro d
  apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => I h w) (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro _
  exact StatePrefixEnsures.bind (r.peerHashtable pid) (fun _ =>
    AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid _ (fun _ => rfl)))

theorem removeByPeerPrefix_preserves_product (c : ProductAmbientContracts I) (hc : ProductNodeStable I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (removeByPeerPrefix pid)) := by
  have branch_spec (d : Decision) (b : Bool) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (Leanux.branch d b))) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)))
  have invariant_spec (α : Type) (why : String) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (Leanux.invariant (α := α) why))) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)))
  simp only [removeByPeerPrefix, liftWGObserver_bind, liftWGObserver_pure, apply_ite, allowed_lift_forIn]
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [allowed_lift_forIn] | rw [Std.Legacy.Range.forIn_eq_forIn_range'] | rw [apply_ite])
    | with_reducible exact ProductAmbientContracts.drop (ProductAmbientContracts.forget (c.getPeer (fun _ => True) _) (fun _ _ hi => hi.1))
    | with_reducible exact ProductAmbientContracts.drop (listDelPrefix_spec_product c (fun _ => True) _)
    | with_reducible exact ProductAmbientContracts.drop (nodeLift_native_product c hc (fun _ => True) _ (removeNodeBody_sameNode _))
    | with_reducible exact nodeModify_preserves_product c hc _ (fun _ => rfl)
    | with_reducible exact branch_spec _ _
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible exact c.safe
    | with_reducible apply PrefixPreserves.forIn
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only; try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite, allowed_lift_forIn, Std.Legacy.Range.forIn_eq_forIn_range'])
    | (with_reducible split)

theorem rootRemovePeerListsPrefix_preserves_product (c : ProductAmbientContracts I) (root : NodeId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (rootRemovePeerListsPrefix root)) := by
  have branch_spec (d : Decision) (b : Bool) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (Leanux.branch d b))) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)))
  have invariant_spec (α : Type) (why : String) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (Leanux.invariant (α := α) why))) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)))
  simp only [rootRemovePeerListsPrefix, liftWGObserver_bind, allowed_lift_forIn, Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [allowed_lift_forIn] | rw [Std.Legacy.Range.forIn_eq_forIn_range'] | rw [apply_ite])
    | with_reducible exact ProductAmbientContracts.drop (ProductAmbientContracts.forget (c.getPeer (fun _ => True) _) (fun _ _ hi => hi.1))
    | with_reducible exact ProductAmbientContracts.drop (listDelPrefix_spec_product c (fun _ => True) _)
    | with_reducible exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ allowed_getDev)
    | with_reducible exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (allowed_readAip (getNode_sameAipStore _)))
    | with_reducible exact branch_spec _ _
    | with_reducible exact invariant_spec _ _
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible exact c.safe
    | with_reducible apply PrefixPreserves.range
    | with_reducible apply PrefixPreserves.forIn
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only; try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite, allowed_lift_forIn, Std.Legacy.Range.forIn_eq_forIn_range'])
    | (with_reducible split)

theorem freeAllowedIpsPrefix_preserves_product (c : ProductAmbientContracts I) (hc : ProductNodeStable I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver freeAllowedIpsPrefix) := by
  have branch_spec (d : Decision) (b : Bool) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (Leanux.branch d b))) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)))
  have invariant_spec (α : Type) (why : String) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (Leanux.invariant (α := α) why))) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)))
  simp only [freeAllowedIpsPrefix, liftWGObserver_bind, liftWGObserver_pure, apply_ite, allowed_lift_forIn]
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [allowed_lift_forIn] | rw [Std.Legacy.Range.forIn_eq_forIn_range'] | rw [apply_ite])
    | with_reducible exact rootRemovePeerListsPrefix_preserves_product c _
    | with_reducible exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ allowed_getDev)
    | with_reducible exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (allowed_readAip (subtree_sameAipStore _)))
    | with_reducible exact ProductAmbientContracts.drop (nodeLift_native_product c hc (fun _ => True) _ (liftAip_sameNode (freeNode_sameNextNode _)))
    | with_reducible exact nodeModify_preserves_product c hc _ (fun _ => rfl)
    | with_reducible exact branch_spec _ _
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible exact c.safe
    | with_reducible apply PrefixPreserves.forIn
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only; try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite, allowed_lift_forIn, Std.Legacy.Range.forIn_eq_forIn_range'])
    | (with_reducible split)

theorem peerMakeDeadPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductAllowedIpsContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (peerMakeDeadPrefix pid)) := by
  simp only [peerMakeDeadPrefix, liftWGObserver_bind]
  apply PrefixPreserves.bind (r.peerList pid)
  intro _
  apply PrefixPreserves.bind (removeByPeerPrefix_preserves_product c r.nodes pid)
  intro _
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ allowed_getDev))
  intro d
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
    (fun initial => hoare_liftAmbient (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid)))
      (fun w => wgStoreView w = initial))))
  intro _
  exact PrefixPreserves.bind (r.peerHashtable pid) (fun _ =>
    ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid _ (fun _ => rfl)))

inductive AllowedIpsCall where
  | append (pid : PeerId) (id : NodeId)
  | deleteList (id : NodeId)
  | removePeer (pid : PeerId)
  | removeRootLists (root : NodeId)
  | free
  | makeDead (pid : PeerId)

namespace AllowedIpsCall

def original : AllowedIpsCall → WG.M Unit
  | .append pid id => listAddTail pid id
  | .deleteList id => listDel id
  | .removePeer pid => removeByPeer pid
  | .removeRootLists root => rootRemovePeerLists root
  | .free => WG.free
  | .makeDead pid => peerMakeDead pid

def observed : AllowedIpsCall → MixedM Unit
  | .append pid id => listAddTailPrefix pid id
  | .deleteList id => listDelPrefix id
  | .removePeer pid => removeByPeerPrefix pid
  | .removeRootLists root => rootRemovePeerListsPrefix root
  | .free => freeAllowedIpsPrefix
  | .makeDead pid => peerMakeDeadPrefix pid

theorem erases (call : AllowedIpsCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | append pid id => exact listAddTailPrefix_erases pid id
  | deleteList id => exact listDelPrefix_erases id
  | removePeer pid => exact removeByPeerPrefix_erases pid
  | removeRootLists root => exact rootRemovePeerListsPrefix_erases root
  | free => exact freeAllowedIpsPrefix_erases
  | makeDead pid => exact peerMakeDeadPrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I) (r : AllowedIpsContracts I) (call : AllowedIpsCall) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | append pid id => exact AmbientContracts.drop (listAddTailPrefix_spec c (fun _ => True) pid id)
  | deleteList id => exact AmbientContracts.drop (listDelPrefix_spec c (fun _ => True) id)
  | removePeer pid => exact removeByPeerPrefix_preserves c r.nodes pid
  | removeRootLists root => exact rootRemovePeerListsPrefix_preserves c root
  | free => exact freeAllowedIpsPrefix_preserves c r.nodes
  | makeDead pid => exact peerMakeDeadPrefix_preserves c r pid

theorem preserves_product (c : ProductAmbientContracts I) (r : ProductAllowedIpsContracts I) (call : AllowedIpsCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | append pid id => exact ProductAmbientContracts.drop (listAddTailPrefix_spec_product c (fun _ => True) pid id)
  | deleteList id => exact ProductAmbientContracts.drop (listDelPrefix_spec_product c (fun _ => True) id)
  | removePeer pid => exact removeByPeerPrefix_preserves_product c r.nodes pid
  | removeRootLists root => exact rootRemovePeerListsPrefix_preserves_product c root
  | free => exact freeAllowedIpsPrefix_preserves_product c r.nodes
  | makeDead pid => exact peerMakeDeadPrefix_preserves_product c r pid

theorem allocation (call : AllowedIpsCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationAllowedIps

end AllowedIpsCall
end Leanux.Proofs.WG.Lifetimes
