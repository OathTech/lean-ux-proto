import Leanux.Proofs.WG.Lifetimes.SavedPeers
import Leanux.Proofs.Logged.PrefixBatch
import Leanux.Proofs.Framing.WGAllowedIps

/-! Complete local allowed-IP list/removal calls. The saved peer-map walk logs
one read for every tested entry and each hit's saved-value write in source order.
Node-only walks retain their original failures and finite exhaustion bounds. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem nodeKernel_identity_metadata (w v : World)
    (he : nodeKernelView v = nodeKernelView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  have hi := congrArg (fun k => identityView {w with k}) he
  have hm := congrArg (fun k => allocationMetadata {w with k}) he
  apply Prod.ext
  · unfold identityView Peers.snapshot keypairResidents packetResidents at hi ⊢
    simpa [nodeKernelView, nodeKernel, nodeDevice, Option.bind_map, Function.comp_def] using hi
  · unfold allocationMetadata deviceAllocationMetadata at hm ⊢
    simpa [nodeKernelView, nodeKernel, nodeDevice, Option.map_map, Function.comp_def] using hm

def NodeStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, nodeKernelView v = nodeKernelView w → I h w → I h v

theorem allocationNodeStable : NodeStable AllocationInv := by
  intro h w v he hi
  have hf := nodeKernel_identity_metadata w v he
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem nodeLift_spec (c : AmbientContracts I) (hc : NodeStable I)
    (P : IdentityView → Prop) (a : M α) (ha : SameNodeKernel a) :
    AmbientSpec I P (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a (fun _ _ hi => c.safe _ _ hi.1)
  intro h w x v hi hr
  have hf := ha w x v hr
  refine ⟨hc h w v hf hi.1, ?_⟩
  have hid : identityView v = identityView w := congrArg Prod.fst (nodeKernel_identity_metadata w v hf)
  change P (identityView v)
  rw [hid]
  exact hi.2

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
  let d ← liftPrefix getDev
  listDelEntriesPrefix id d.peers.toList

theorem listAddTailPrefix_erases (pid : PeerId) (id : NodeId) :
    ErasesPrefix (listAddTailPrefix pid id) (listAddTail pid id) :=
  erasesPrefix_bind (getPeerMixed_erases pid) (fun _ => setPeerMixed_erases _ _)

theorem listDelEntriesPrefix_erases (id : NodeId) (xs : List (PeerId × Peer)) :
    ErasesPrefix (listDelEntriesPrefix id xs) (do
      for (pid,p) in xs do
        if p.allowedipsList.contains id then
          setPeer pid {p with allowedipsList := listRemove p.allowedipsList id}) := by
  induction xs with
  | nil => exact erasesPrefix_pure _
  | cons x xs ih =>
    rcases x with ⟨pid,p⟩
    simp only [List.forIn_cons]
    unfold listDelEntriesPrefix
    apply erasesPrefix_bind_pure (erasesPrefix_emit _)
    cases ht : p.allowedipsList.contains id <;>
      simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
    · exact ih
    · exact erasesPrefix_bind (setPeerMixed_erases pid _) (fun _ => ih)

theorem listDelPrefix_erases (id : NodeId) : ErasesPrefix (listDelPrefix id) (listDel id) :=
  erasesPrefix_bind (erasesPrefix_lift _) (fun d => listDelEntriesPrefix_erases id d.peers.toList)

theorem listAddTailPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (id : NodeId) : AmbientSpec I P (listAddTailPrefix pid id) (fun _ => P) :=
  PrefixEnsures.bind (c.getPeer P pid) (fun p => c.setPeer P pid {p with allowedipsList := p.allowedipsList ++ [id]})

theorem listDelEntriesPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (id : NodeId) (xs : List (PeerId × Peer)) :
    AmbientSpec I (fun s => P s ∧ SavedPeers xs s) (listDelEntriesPrefix id xs) (fun _ => P) := by
  induction xs with
  | nil =>
    exact (c.pure (fun s => P s ∧ SavedPeers [] s) ()).consequence
      (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, hi.2.1⟩)
  | cons x xs ih =>
    rcases x with ⟨pid,p⟩
    unfold listDelEntriesPrefix
    have hread : AmbientSpec I (fun s => P s ∧ SavedPeers ((pid,p)::xs) s)
        (savedPeerRead pid p) (fun _ s => (P s ∧ SavedPeers xs s) ∧ s.1.slots pid = some p.internalId) :=
      (savedPeerRead_spec c (fun s => P s ∧ SavedPeers xs s) pid p).consequence
      (fun _ _ hi => ⟨hi.1, ⟨hi.2.1, fun i q hq => hi.2.2 i q (by simp [hq])⟩,
        hi.2.2 pid p (by simp)⟩) (fun _ _ _ hi => hi)
    apply PrefixEnsures.bind hread
    intro _
    split
    · exact PrefixEnsures.bind
        (c.setPeer (fun s => P s ∧ SavedPeers xs s) pid
          {p with allowedipsList := listRemove p.allowedipsList id}) (fun _ => ih)
    · exact ih.consequence (fun _ _ hi => ⟨hi.1, hi.2.1⟩) (fun _ _ _ hi => hi)

theorem listDelPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (id : NodeId) :
    AmbientSpec I P (listDelPrefix id) (fun _ => P) :=
  PrefixEnsures.bind (getDev_saved_spec c P) (fun d => listDelEntriesPrefix_spec c P id d.peers.toList)

def removeByPeerPrefix (pid : PeerId) : MixedM Unit := do
  let p ← getPeerMixed pid
  if ← liftPrefix (branch .removeListEmpty p.allowedipsList.isEmpty) then return
  liftPrefix (modifyDev fun d => {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}})
  let _ ← forIn p.allowedipsList () (fun id _ => do
    _ ← liftPrefix (branch .removeListIter true)
    listDelPrefix id
    liftPrefix (AllowedIps.removeNodeBody id))
  _ ← liftPrefix (branch .removeListIter false)

def rootRemovePeerListsPrefix (root : NodeId) : MixedM Unit := do
  let mut stack := [root]
  for _ in [0:(← liftPrefix getDev).nodes.size + 1] do
    match stack with
    | [] => do _ ← liftPrefix (branch .rootRemoveLenPositive false); return
    | id :: rest =>
      _ ← liftPrefix (branch .rootRemoveLenPositive true)
      _ ← liftPrefix (branch .rootRemovePopped true)
      stack := rest
      let n ← liftPrefix (getNode id)
      for c in n.bit.toList do
        if ← liftPrefix (branch .pushRcuNonNull c.isSome) then
          if let some c := c then stack := c :: stack
      if ← liftPrefix (branch .rootRemoveHasPeer n.peer.isSome) then
        let some pid := n.peer | liftPrefix (invariant "unreachable")
        if !(← getPeerMixed pid).allowedipsList.contains id then
          liftPrefix (invariant "trie node missing from its peer's list")
        listDelPrefix id
  liftPrefix (invariant "root_remove_peer_lists did not terminate")

def freeAllowedIpsPrefix : MixedM Unit := do
  let t := (← liftPrefix getDev).peerAllowedips
  liftPrefix (modifyDev fun d => {d with peerAllowedips := {root4 := none, root6 := none, seq := t.seq + 1}})
  for (old, d) in [(t.root4, Decision.freeHasRoot4), (t.root6, Decision.freeHasRoot6)] do
    if ← liftPrefix (branch d old.isSome) then
      if let some root := old then
        rootRemovePeerListsPrefix root
        for id in ← liftPrefix (subtree root) do liftPrefix (freeNode id)

def deadPeerList (pid : PeerId) (d : Device) : Device :=
  {d with peerList := d.peerList.filter (· != pid)}
def deadPeerHashtable (pid : PeerId) (d : Device) : Device :=
  {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}

def peerMakeDeadPrefix (pid : PeerId) : MixedM Unit := do
  liftPrefix (modifyDev (deadPeerList pid))
  removeByPeerPrefix pid
  liftPrefix (modifyDev (deadPeerHashtable pid))
  modifyPeerKeysPrefix pid fun p => {p with isDead := true}

theorem removeByPeerPrefix_erases (pid : PeerId) :
    ErasesPrefix (removeByPeerPrefix pid) (removeByPeer pid) := by
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold removeByPeerPrefix AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact listDelPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem rootRemovePeerListsPrefix_erases (root : NodeId) :
    ErasesPrefix (rootRemovePeerListsPrefix root) (rootRemovePeerLists root) := by
  unfold rootRemovePeerListsPrefix rootRemovePeerLists
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact listDelPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

  all_goals simp_all only [List.cons.injEq, Option.some.injEq, reduceCtorEq, forall_eq']
  all_goals subst_vars
  all_goals repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact listDelPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem freeAllowedIpsPrefix_erases : ErasesPrefix freeAllowedIpsPrefix free := by
  unfold freeAllowedIpsPrefix free
  repeat' first
    | with_reducible exact rootRemovePeerListsPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

  all_goals simp_all only [Option.some.injEq, forall_eq']
  all_goals subst_vars
  all_goals first | exact rootRemovePeerListsPrefix_erases _ | exact erasesPrefix_lift _ | exact erasesPrefix_pure _

theorem peerMakeDeadPrefix_erases (pid : PeerId) : ErasesPrefix (peerMakeDeadPrefix pid) (peerMakeDead pid) := by
  unfold peerMakeDeadPrefix peerMakeDead modifyPeerKeysPrefix
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
    erasesPrefix_bind (removeByPeerPrefix_erases pid) (fun _ =>
      erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
        erasesPrefix_bind (getPeerMixed_erases pid) (fun _ => setPeerMixed_erases _ _))))


/-- Scalar peer-list/hash bookkeeping is separate from the node-only mask. -/
structure AllowedIpsContracts (I : List LifetimeEvent → World → Prop) : Prop where
  nodes : NodeStable I
  peerList : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (modifyDev (deadPeerList pid)))
  peerHashtable : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (modifyDev (deadPeerHashtable pid)))

theorem allocationAllowedIps : AllowedIpsContracts AllocationInv := by
  constructor
  · exact allocationNodeStable
  all_goals
    intro pid
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
    intro h w x v hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [deadPeerList, deadPeerHashtable, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, deadPeerList,
        deadPeerHashtable, Option.map_map, Function.comp_def] <;> rfl

theorem nodeModify_preserves (c : AmbientContracts I) (hc : NodeStable I)
    (f : Device → Device) (hf : ∀ d, nodeDevice (f d) = nodeDevice d) :
    PrefixPreserves I LifetimeEvent.Safe (liftPrefix (modifyDev f)) :=
  AmbientContracts.drop (nodeLift_spec c hc (fun _ => True) _
    (by apply SameView.of_wp; intro initial; exact modifyDev_node_spec (fun s => s = initial) f hf))

theorem removeByPeerPrefix_preserves (c : AmbientContracts I) (hc : NodeStable I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (removeByPeerPrefix pid) := by
  unfold removeByPeerPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (listDelPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (nodeLift_spec c hc (fun _ => True) _ (removeNodeBody_sameNodeKernel _))
    | with_reducible exact nodeModify_preserves c hc _ (fun _ => rfl)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible exact c.safe
    | with_reducible apply PrefixPreserves.forIn
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem rootRemovePeerListsPrefix_preserves (c : AmbientContracts I) (root : NodeId) :
    PrefixPreserves I LifetimeEvent.Safe (rootRemovePeerListsPrefix root) := by
  unfold rootRemovePeerListsPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (listDelPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.getNode_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible exact c.safe
    | with_reducible apply PrefixPreserves.range
    | with_reducible apply PrefixPreserves.forIn
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem freeAllowedIpsPrefix_preserves (c : AmbientContracts I) (hc : NodeStable I) :
    PrefixPreserves I LifetimeEvent.Safe freeAllowedIpsPrefix := by
  unfold freeAllowedIpsPrefix
  repeat' first
    | with_reducible exact rootRemovePeerListsPrefix_preserves c _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (subtree_sameKernel _))
    | with_reducible exact AmbientContracts.drop (nodeLift_spec c hc (fun _ => True) _ (freeNode_sameNodeKernel _))
    | with_reducible exact nodeModify_preserves c hc _ (fun _ => rfl)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible exact c.safe
    | with_reducible apply PrefixPreserves.forIn
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem peerMakeDeadPrefix_preserves (c : AmbientContracts I) (r : AllowedIpsContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (peerMakeDeadPrefix pid) := by
  unfold peerMakeDeadPrefix
  exact PrefixPreserves.bind (r.peerList pid) (fun _ =>
    PrefixPreserves.bind (removeByPeerPrefix_preserves c r.nodes pid) (fun _ =>
      PrefixPreserves.bind (r.peerHashtable pid) (fun _ =>
        AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid _ (fun _ => rfl)))))

inductive AllowedIpsCall where
  | append (pid : PeerId) (id : NodeId)
  | deleteList (id : NodeId)
  | removePeer (pid : PeerId)
  | removeRootLists (root : NodeId)
  | free
  | makeDead (pid : PeerId)

namespace AllowedIpsCall

def original : AllowedIpsCall → M Unit
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

theorem erases (call : AllowedIpsCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | append pid id => exact listAddTailPrefix_erases pid id
  | deleteList id => exact listDelPrefix_erases id
  | removePeer pid => exact removeByPeerPrefix_erases pid
  | removeRootLists root => exact rootRemovePeerListsPrefix_erases root
  | free => exact freeAllowedIpsPrefix_erases
  | makeDead pid => exact peerMakeDeadPrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I) (r : AllowedIpsContracts I) (call : AllowedIpsCall) :
    PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | append pid id => exact AmbientContracts.drop (listAddTailPrefix_spec c (fun _ => True) pid id)
  | deleteList id => exact AmbientContracts.drop (listDelPrefix_spec c (fun _ => True) id)
  | removePeer pid => exact removeByPeerPrefix_preserves c r.nodes pid
  | removeRootLists root => exact rootRemovePeerListsPrefix_preserves c root
  | free => exact freeAllowedIpsPrefix_preserves c r.nodes
  | makeDead pid => exact peerMakeDeadPrefix_preserves c r pid

theorem allocation (call : AllowedIpsCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationAllowedIps

end AllowedIpsCall
end Leanux.Proofs.WG.Lifetimes
