import Leanux.Proofs.WG.Lifetimes.AllowedIpsAccess
import Leanux.Proofs.Framing.WGAllowedIpsInsert

/-! Complete original allowed-IP insertion with source-order peer list reads
and writes. Node-only leaves are lifted after a separate source access audit.
No address bound, representation, resident target or successful-run premise is
needed for erasure or allocation-access safety. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

def addAllowedIpPrefix (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) : MixedM Int := do
  if ← liftPrefix (branchCmp .addCidrTooLong (cidr > bits) cidr bits) then return -EINVAL
  if ← liftPrefix (branch .addNoPeer peer.isNone) then return -EINVAL
  let some pid := peer | liftPrefix (invariant "unreachable")
  let trie ← liftPrefix (slotGet root)
  if ← liftPrefix (branch .addEmptyTrie trie.isNone) then
    let some id ← (do
        let r ← liftPrefix (allocNode .allocNode190 (newNode key cidr bits (some pid)))
        if ← liftPrefix (branch .addRootNoMem r.isNone) then return none
        pure r) | return -ENOMEM
    listAddTailPrefix pid id
    liftPrefix (connectNode root id)
    return 0
  let (placed, exact) ← liftPrefix (nodePlacement trie key cidr bits)
  if ← liftPrefix (branch .addExact exact) then
    let some id := placed | liftPrefix (invariant "exact placement without a node")
    liftPrefix (setNode id { (← liftPrefix (getNode id)) with peer := some pid })
    listDelPrefix id
    listAddTailPrefix pid id
    return 0
  let newnodeAlloc ← liftPrefix (allocNode .allocNode205 (newNode key cidr bits (some pid)))
  if ← liftPrefix (branch .addNewnodeNoMem newnodeAlloc.isNone) then return -ENOMEM
  let some newnode := newnodeAlloc | liftPrefix (invariant "unreachable")
  listAddTailPrefix pid newnode
  let down ← do
    if ← liftPrefix (branch .addNoParentNode placed.isNone) then liftPrefix (slotGet root)
    else
      let some node := placed | liftPrefix (invariant "unreachable")
      let bit ← liftPrefix (choose (← liftPrefix (getNode node)) key)
      let down ← liftPrefix ((← liftPrefix (getNode node)).bitAt bit)
      if ← liftPrefix (branch .addNoDown down.isNone) then
        liftPrefix (connectNode (.child node bit) newnode)
        return 0
      pure down
  let some downId := down | liftPrefix (invariant "add: no node below the placement")
  let common ← liftPrefix (commonBits (← liftPrefix (getNode downId)) key bits)
  let cidr := min cidr common
  let parent := placed
  if ← liftPrefix (branch .addNewnodeCoversDown ((← liftPrefix (getNode newnode)).cidr == cidr)) then
    liftPrefix (chooseAndConnectNode newnode downId)
    if ← liftPrefix (branch .addNewnodeAtRoot parent.isNone) then liftPrefix (connectNode root newnode)
    else if let some p := parent then liftPrefix (chooseAndConnectNode p newnode)
    return 0
  let nodeAlloc ← liftPrefix (allocNode .allocNode234 (newNode (← liftPrefix (getNode newnode)).bits cidr bits none))
  if ← liftPrefix (branch .addIntermediateNoMem nodeAlloc.isNone) then
    listDelPrefix newnode
    liftPrefix (freeNode newnode)
    return -ENOMEM
  let some node := nodeAlloc | liftPrefix (invariant "unreachable")
  liftPrefix (chooseAndConnectNode node downId)
  liftPrefix (chooseAndConnectNode node newnode)
  if ← liftPrefix (branch .addIntermediateAtRoot parent.isNone) then liftPrefix (connectNode root node)
  else if let some p := parent then liftPrefix (chooseAndConnectNode p node)
  return 0

def insertAllowedIpPrefix (family addr cidr : Nat) (peer : PeerId) : MixedM Int := do
  liftPrefix (modifyDev fun d => {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}})
  if family == 4 then addAllowedIpPrefix .root4 32 addr cidr (some peer)
  else addAllowedIpPrefix .root6 128 addr cidr (some peer)

theorem addAllowedIpPrefix_erases (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    ErasesPrefix (addAllowedIpPrefix root bits key cidr peer) (add root bits key cidr peer) := by
  unfold addAllowedIpPrefix add
  repeat' first
    | with_reducible exact listAddTailPrefix_erases _ _
    | with_reducible exact listDelPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first
    | exact erasesPrefix_lift _
    | exact listDelPrefix_erases _
    | exact listAddTailPrefix_erases _ _
    | exact erasesPrefix_pure _

theorem insertAllowedIpPrefix_erases (family addr cidr : Nat) (peer : PeerId) :
    ErasesPrefix (insertAllowedIpPrefix family addr cidr peer) (WG.insert family addr cidr peer) := by
  unfold insertAllowedIpPrefix WG.insert
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro _
  split
  · exact addAllowedIpPrefix_erases .root4 32 addr cidr (some peer)
  · exact addAllowedIpPrefix_erases .root6 128 addr cidr (some peer)

theorem nodeAllocation_identity_metadata (w v : World)
    (he : nodeAllocationView v = nodeAllocationView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  have hi := congrArg (fun k => identityView {w with k}) he
  have hm := congrArg (fun k => allocationMetadata {w with k}) he
  apply Prod.ext
  · unfold identityView Peers.snapshot keypairResidents packetResidents at hi ⊢
    simpa [nodeAllocationView, nodeAllocationKernel, nodeAllocationDevice, nodeDevice,
      Option.bind_map, Function.comp_def] using hi
  · unfold allocationMetadata deviceAllocationMetadata at hm ⊢
    simpa [nodeAllocationView, nodeAllocationKernel, nodeAllocationDevice, nodeDevice,
      Option.map_map, Function.comp_def] using hm

def NodeAllocationStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, nodeAllocationView v = nodeAllocationView w → I h w → I h v

theorem allocationNodeAllocationStable : NodeAllocationStable AllocationInv := by
  intro h w v he hi
  have hf := nodeAllocation_identity_metadata w v he
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem nodeAllocationLift_spec (c : AmbientContracts I) (hc : NodeAllocationStable I)
    (P : IdentityView → Prop) (a : M α) (ha : SameNodeAllocation a) :
    AmbientSpec I P (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a (fun _ _ hi => c.safe _ _ hi.1)
  intro h w x v hi hr
  have hf := ha w x v hr
  refine ⟨hc h w v hf hi.1, ?_⟩
  have hid : identityView v = identityView w :=
    congrArg Prod.fst (nodeAllocation_identity_metadata w v hf)
  change P (identityView v)
  rw [hid]
  exact hi.2

theorem addAllowedIpPrefix_preserves (c : AmbientContracts I) (hc : NodeAllocationStable I)
    (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (addAllowedIpPrefix root bits key cidr peer) := by
  unfold addAllowedIpPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (listAddTailPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (listDelPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (nodeAllocationLift_spec c hc (fun _ => True) _ (allocNode_sameNodeAllocation _ _))
    | with_reducible exact AmbientContracts.drop (nodeAllocationLift_spec c hc (fun _ => True) _ (connectNode_sameNodeKernel _ _).allocation)
    | with_reducible exact AmbientContracts.drop (nodeAllocationLift_spec c hc (fun _ => True) _ (chooseAndConnectNode_sameNodeKernel _ _).allocation)
    | with_reducible exact AmbientContracts.drop (nodeAllocationLift_spec c hc (fun _ => True) _ (setNode_sameNodeKernel _ _).allocation)
    | with_reducible exact AmbientContracts.drop (nodeAllocationLift_spec c hc (fun _ => True) _ (freeNode_sameNodeKernel _).allocation)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (slotGet_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (getNode_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (aipBitAt_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (choose_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (commonBits_sameKernel _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (nodePlacement_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.branchCmp (fun _ => True) _ _ _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem insertAllowedIpPrefix_preserves (c : AmbientContracts I) (hc : NodeAllocationStable I)
    (family addr cidr : Nat) (peer : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (insertAllowedIpPrefix family addr cidr peer) := by
  unfold insertAllowedIpPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (nodeAllocationLift_spec c hc (fun _ => True) _ ?_))
  · intro _
    split
    · exact addAllowedIpPrefix_preserves c hc .root4 32 addr cidr (some peer)
    · exact addAllowedIpPrefix_preserves c hc .root6 128 addr cidr (some peer)
  · apply SameView.of_wp
    intro s
    exact modifyDev_nodeAllocation_spec (fun t => t = s) _ (fun _ => rfl)

inductive AllowedIpsInsertCall where
  | add (root : Slot) (bits key cidr : Nat) (peer : Option PeerId)
  | insert (family addr cidr : Nat) (peer : PeerId)

namespace AllowedIpsInsertCall

def original : AllowedIpsInsertCall → M Int
  | .add root bits key cidr peer => WG.add root bits key cidr peer
  | .insert family addr cidr peer => WG.insert family addr cidr peer

def observed : AllowedIpsInsertCall → MixedM Int
  | .add root bits key cidr peer => addAllowedIpPrefix root bits key cidr peer
  | .insert family addr cidr peer => insertAllowedIpPrefix family addr cidr peer

theorem erases (call : AllowedIpsInsertCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | add root bits key cidr peer => exact addAllowedIpPrefix_erases root bits key cidr peer
  | insert family addr cidr peer => exact insertAllowedIpPrefix_erases family addr cidr peer

theorem preserves_ambient (c : AmbientContracts I) (hc : NodeAllocationStable I)
    (call : AllowedIpsInsertCall) : PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | add root bits key cidr peer => exact addAllowedIpPrefix_preserves c hc root bits key cidr peer
  | insert family addr cidr peer => exact insertAllowedIpPrefix_preserves c hc family addr cidr peer

theorem allocation (call : AllowedIpsInsertCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationNodeAllocationStable

end AllowedIpsInsertCall
end Leanux.Proofs.WG.Lifetimes
