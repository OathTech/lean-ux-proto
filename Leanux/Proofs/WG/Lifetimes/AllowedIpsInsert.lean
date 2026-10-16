import Leanux.Proofs.WG.Lifetimes.AllowedIpsAccess
import Leanux.Proofs.Framing.WGAllowedIpsInsert
import Leanux.Proofs.WG.Lifetimes.MaintenanceTimers

/-! Complete original allowed-IP insertion with source-order peer list reads
and writes. Node-only leaves are lifted after a separate source access audit.
No address bound, representation, resident target or successful-run premise is
needed for erasure or allocation-access safety. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

def addAllowedIpPrefix (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) : MixedM Int := do
  if ← liftWGPrefix (branchCmp .addCidrTooLong (cidr > bits) cidr bits) then return -EINVAL
  if ← liftWGPrefix (branch .addNoPeer peer.isNone) then return -EINVAL
  let some pid := peer | liftWGPrefix (invariant "unreachable")
  let trie ← liftWGPrefix (liftAip (slotGet root))
  if ← liftWGPrefix (branch .addEmptyTrie trie.isNone) then
    let some id ← (do
        let r ← liftWGPrefix (liftAip (allocNode .allocNode190 (newNode key cidr bits (some pid))))
        if ← liftWGPrefix (branch .addRootNoMem r.isNone) then return none
        pure r) | return -ENOMEM
    listAddTailPrefix pid id
    liftWGPrefix (liftAip (connectNode root id))
    return 0
  let (placed, exact) ← liftWGPrefix (liftAip (nodePlacement trie key cidr bits))
  if ← liftWGPrefix (branch .addExact exact) then
    let some id := placed | liftWGPrefix (invariant "exact placement without a node")
    liftWGPrefix (liftAip (setNode id { (← liftWGPrefix (liftAip (getNode id))) with peer := some pid }))
    listDelPrefix id
    listAddTailPrefix pid id
    return 0
  let newnodeAlloc ← liftWGPrefix (liftAip (allocNode .allocNode205 (newNode key cidr bits (some pid))))
  if ← liftWGPrefix (branch .addNewnodeNoMem newnodeAlloc.isNone) then return -ENOMEM
  let some newnode := newnodeAlloc | liftWGPrefix (invariant "unreachable")
  listAddTailPrefix pid newnode
  let down ← do
    if ← liftWGPrefix (branch .addNoParentNode placed.isNone) then liftWGPrefix (liftAip (slotGet root))
    else
      let some node := placed | liftWGPrefix (invariant "unreachable")
      let bit ← liftWGPrefix (choose (← liftWGPrefix (liftAip (getNode node))) key)
      let down ← liftWGPrefix ((← liftWGPrefix (liftAip (getNode node))).bitAt bit)
      if ← liftWGPrefix (branch .addNoDown down.isNone) then
        liftWGPrefix (liftAip (connectNode (.child node bit) newnode))
        return 0
      pure down
  let some downId := down | liftWGPrefix (invariant "add: no node below the placement")
  let common ← liftWGPrefix (commonBits (← liftWGPrefix (liftAip (getNode downId))) key bits)
  let cidr := min cidr common
  let parent := placed
  if ← liftWGPrefix (branch .addNewnodeCoversDown ((← liftWGPrefix (liftAip (getNode newnode))).cidr == cidr)) then
    liftWGPrefix (liftAip (chooseAndConnectNode newnode downId))
    if ← liftWGPrefix (branch .addNewnodeAtRoot parent.isNone) then liftWGPrefix (liftAip (connectNode root newnode))
    else if let some p := parent then liftWGPrefix (liftAip (chooseAndConnectNode p newnode))
    return 0
  let nodeAlloc ← liftWGPrefix (liftAip (allocNode .allocNode234 (newNode (← liftWGPrefix (liftAip (getNode newnode))).bits cidr bits none)))
  if ← liftWGPrefix (branch .addIntermediateNoMem nodeAlloc.isNone) then
    listDelPrefix newnode
    liftWGPrefix (liftAip (freeNode newnode))
    return -ENOMEM
  let some node := nodeAlloc | liftWGPrefix (invariant "unreachable")
  liftWGPrefix (liftAip (chooseAndConnectNode node downId))
  liftWGPrefix (liftAip (chooseAndConnectNode node newnode))
  if ← liftWGPrefix (branch .addIntermediateAtRoot parent.isNone) then liftWGPrefix (liftAip (connectNode root node))
  else if let some p := parent then liftWGPrefix (liftAip (chooseAndConnectNode p node))
  return 0

def insertAllowedIpPrefix (family addr cidr : Nat) (peer : PeerId) : MixedM Int := do
  liftWGPrefix (modifyDev fun d => {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}})
  if family == 4 then addAllowedIpPrefix .root4 32 addr cidr (some peer)
  else addAllowedIpPrefix .root6 128 addr cidr (some peer)

private theorem insert_erase_ite {α : Type} (p : Prop) [Decidable p]
    {g h : MixedM α} {a b : WG.M α}
    (hg : p → ErasesStatePrefix g a) (hh : ¬p → ErasesStatePrefix h b) :
    ErasesStatePrefix (if p then g else h) (if p then a else b) := by
  split <;> simp_all

private theorem insert_state_ite {α : Type} {I : List LifetimeEvent → WGWorld → Prop}
    (p : Prop) [Decidable p] {a b : MixedM α}
    (ha : p → StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe a)
    (hb : ¬p → StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe b) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (if p then a else b) := by
  split <;> simp_all

theorem addAllowedIpPrefix_erases (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    ErasesStatePrefix (addAllowedIpPrefix root bits key cidr peer) (add root bits key cidr peer) := by
  unfold addAllowedIpPrefix add
  repeat' first
    | with_reducible exact listAddTailPrefix_erases _ _
    | with_reducible exact listDelPrefix_erases _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply insert_erase_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first
    | exact erasesStatePrefix_lift _
    | exact listDelPrefix_erases _
    | exact listAddTailPrefix_erases _ _
    | exact erasesStatePrefix_pure _

theorem insertAllowedIpPrefix_erases (family addr cidr : Nat) (peer : PeerId) :
    ErasesStatePrefix (insertAllowedIpPrefix family addr cidr peer) (WG.insert family addr cidr peer) := by
  unfold insertAllowedIpPrefix WG.insert
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  split
  · exact addAllowedIpPrefix_erases .root4 32 addr cidr (some peer)
  · exact addAllowedIpPrefix_erases .root6 128 addr cidr (some peer)

theorem nodeAllocation_identity_metadata (w v : WGWorld)
    (he : nodeAllocationView v = nodeAllocationView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  let observe : WGStoreView → IdentityView × AllocationMetadata := fun s =>
    ((⟨s.peerCounter, fun i => (s.dev.bind fun d => d.peers[i]?).map (·.internalId)⟩,
      (fun i => (s.dev.bind fun d => d.keypairs[i]?).map (·.internalId)),
      fun slot => s.dev.bind fun d => match slot with
        | .inl i => d.txSkbs[i]?.map (fun _ => (d.ifindex, i + 1))
        | .inr i => d.rxSkbs[i]?.map (fun _ => (d.ifindex, i + 1))),
      ⟨s.keypairCounter, s.netIfindexNext, s.dev.map deviceAllocationMetadata⟩)
  have factor (g : WGWorld) : observe (nodeAllocationView g) = (identityView g, allocationMetadata g) := by
    unfold identityView keypairResidents packetResidents allocationMetadata
    cases hg : g.dev <;>
      simp [observe, nodeAllocationView, wgStoreView, nodeAllocationDevice, nodeDevice, identityView, Peers.snapshot,
        Leanux.Proofs.WG.Lifetimes.keypairResidents, Leanux.Proofs.WG.Lifetimes.packetResidents,
        allocationMetadata, deviceAllocationMetadata, hg]
    all_goals rfl
  simpa only [factor] using congrArg observe he

def NodeAllocationStable (I : List LifetimeEvent → WGWorld → Prop) : Prop :=
  ∀ h w v, nodeAllocationView v = nodeAllocationView w → I h w → I h v

theorem allocationNodeAllocationStable : NodeAllocationStable AllocationInv := by
  intro h w v he hi
  have hf := nodeAllocation_identity_metadata w v he
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem nodeAllocationLift_spec (c : AmbientContracts I) (hc : NodeAllocationStable I)
    (P : IdentityView → Prop) (a : WG.M α) (ha : SameNodeAllocation a) :
    AmbientSpec I P (liftWGPrefix a) (fun _ => P) := by
  apply StatePrefixEnsures.lift a (fun h w _ hi => c.safe h w hi.1)
  intro h w ambient x v ambient' hi hr
  have hf := (ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr
  refine ⟨hc h w v hf hi.1, ?_⟩
  have hid : identityView v = identityView w :=
    congrArg Prod.fst (nodeAllocation_identity_metadata w v hf)
  change P (identityView v)
  rw [hid]
  exact hi.2

/-- The original product view preserves the other subsystem stores. -/
def productNodeAllocationView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter), nodeAllocationView w.wg)

def ProductNodeAllocationStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, productNodeAllocationView v = productNodeAllocationView w → I h w → I h v

theorem nodeAllocationLift_spec_product (c : ProductAmbientContracts I)
    (hc : ProductNodeAllocationStable I) (P : IdentityView → Prop)
    (a : Leanux.M α) (ha : SameView productNodeAllocationView a) :
    ProductAmbientSpec I P (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a (fun h w hi => c.safe h w hi.1)
  intro h w x v hi hr
  have hf := (ProjectedAction.iff_run _ _ _).mp ha w x v hr
  refine ⟨hc h w v hf hi.1, ?_⟩
  have hid : identityView v.wg = identityView w.wg := congrArg Prod.fst
    (nodeAllocation_identity_metadata w.wg v.wg
      (congrArg (fun s : ProductStore43 => s.2.2.2) hf))
  change P (identityView v.wg)
  rw [hid]
  exact hi.2

private theorem nodeAllocationLift_native_product (c : ProductAmbientContracts I)
    (hc : ProductNodeAllocationStable I) (P : IdentityView → Prop)
    (a : WG.M α) (ha : SameNodeAllocation a) :
    ProductAmbientSpec I P (liftWGObserver (liftWGPrefix a)) (fun _ => P) := by
  rw [liftWGObserver_lift]
  apply nodeAllocationLift_spec_product c hc P
  exact sameView_liftWG productNodeAllocationView nodeAllocationView a ha
    (fun w g ambient he => by simp only [productNodeAllocationView, he])

theorem addAllowedIpPrefix_preserves (c : AmbientContracts I) (hc : NodeAllocationStable I)
    (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (addAllowedIpPrefix root bits key cidr peer) := by
  have aip (α : Type) (a : AipM α) : SameNodeAllocation (liftAip a) := by
    intro initial
    exact hoare_liftAip a (fun w => nodeAllocationView w = initial) (by
      intro g d store hg hd
      simpa [nodeAllocationView, nodeAllocationDevice, nodeDevice, wgStoreView, hd] using hg)
  have pure_ok {α : Type} (x : α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (pure x : MixedM α) :=
    StatePrefixEnsures.pure x (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
  have ambient_ok {α : Type} (a : WG.M α) (ha : SameWGStore a) :=
    AmbientContracts.drop (c.store (fun _ => True) a ha)
  unfold addAllowedIpPrefix
  repeat' first
    | unfold StatePrefixPreserves
    | (maintenance_head listAddTailPrefix; exact AmbientContracts.drop (listAddTailPrefix_spec c (fun _ => True) _ _))
    | (maintenance_head listDelPrefix; exact AmbientContracts.drop (listDelPrefix_spec c (fun _ => True) _))
    | (maintenance_lift_action_head liftAip; exact AmbientContracts.drop (nodeAllocationLift_spec c hc (fun _ => True) _ (aip _ _)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.branch (fun _ => True) _ _))
    | (maintenance_lift_action_head branchCmp; exact AmbientContracts.drop (c.branchCmp (fun _ => True) _ _ _ _))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.invariant (fun _ => True) _))
    | (maintenance_head Pure.pure; exact pure_ok _)
    | (maintenance_lift_action_head choose; exact ambient_ok (choose _ _) (by intro initial; unfold Hoare; mvcgen [choose, invariant, AmbientM.invariant]))
    | (maintenance_lift_action_head AipNode.bitAt; exact ambient_ok (AipNode.bitAt _ _) (by intro initial; unfold Hoare; mvcgen [AipNode.bitAt, invariant, AmbientM.invariant]))
    | (maintenance_lift_action_head commonBits; exact ambient_ok (commonBits _ _ _) (by intro initial; unfold Hoare; mvcgen [commonBits, branch, AmbientM.branch]))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => I h w))
    | (maintenance_head ite; apply insert_state_ite)
    | (maintenance_intro; try dsimp only)
    | split

theorem insertAllowedIpPrefix_preserves (c : AmbientContracts I) (hc : NodeAllocationStable I)
    (family addr cidr : Nat) (peer : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (insertAllowedIpPrefix family addr cidr peer) := by
  unfold insertAllowedIpPrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (nodeAllocationLift_spec c hc (fun _ => True) _ ?_))
  · intro _
    split
    · exact addAllowedIpPrefix_preserves c hc .root4 32 addr cidr (some peer)
    · exact addAllowedIpPrefix_preserves c hc .root6 128 addr cidr (some peer)
  · apply SameView.of_wp
    intro s
    exact modifyDev_nodeAllocation_spec (fun t => t = s) _ (fun _ => rfl)

theorem addAllowedIpPrefix_preserves_product (c : ProductAmbientContracts I)
    (hc : ProductNodeAllocationStable I)
    (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (addAllowedIpPrefix root bits key cidr peer)) := by
  have aip (α : Type) (a : AipM α) : SameNodeAllocation (liftAip a) := by
    intro initial
    exact hoare_liftAip a (fun w => nodeAllocationView w = initial) (by
      intro g d store hg hd
      simpa [nodeAllocationView, nodeAllocationDevice, nodeDevice, wgStoreView, hd] using hg)
  have ambient_ok {α : Type} (a : WG.M α) (ha : SameWGStore a) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) a ha)
  have conditional {α : Type} (p : Prop) [Decidable p] {a b : PrefixM LifetimeEvent α}
      (ha : p → PrefixEnsures I LifetimeEvent.Safe a (fun _ => I))
      (hb : ¬p → PrefixEnsures I LifetimeEvent.Safe b (fun _ => I)) :
      PrefixEnsures I LifetimeEvent.Safe (if p then a else b) (fun _ => I) := by
    split <;> simp_all
  have lifted_conditional {α : Type} (p : Prop) [Decidable p] {a b : MixedM α}
      (ha : p → PrefixEnsures I LifetimeEvent.Safe (liftWGObserver a) (fun _ => I))
      (hb : ¬p → PrefixEnsures I LifetimeEvent.Safe (liftWGObserver b) (fun _ => I)) :
      PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (if p then a else b)) (fun _ => I) := by
    split <;> simp_all
  change PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I)
  unfold addAllowedIpPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [apply_ite])
    | (maintenance_head listAddTailPrefix; exact ProductAmbientContracts.drop (listAddTailPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head listDelPrefix; exact ProductAmbientContracts.drop (listDelPrefix_spec_product c (fun _ => True) _))
    | (maintenance_lift_action_head liftAip; exact ProductAmbientContracts.drop (nodeAllocationLift_native_product c hc (fun _ => True) _ (aip _ _)))
    | (maintenance_lift_action_head branch; exact ambient_ok (branch _ _) (by intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) _))
    | (maintenance_lift_action_head branchCmp; exact ambient_ok (branchCmp _ _ _ _) (by intro initial; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) _))
    | (maintenance_lift_action_head invariant; exact ambient_ok (invariant _) (by intro initial; exact hoare_liftAmbient (AmbientM.invariant _) _))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_lift_action_head choose; exact ambient_ok (choose _ _) (by intro initial; unfold Hoare; mvcgen [choose, invariant, AmbientM.invariant]))
    | (maintenance_lift_action_head AipNode.bitAt; exact ambient_ok (AipNode.bitAt _ _) (by intro initial; unfold Hoare; mvcgen [AipNode.bitAt, invariant, AmbientM.invariant]))
    | (maintenance_lift_action_head commonBits; exact ambient_ok (commonBits _ _ _) (by intro initial; unfold Hoare; mvcgen [commonBits, branch, AmbientM.branch]))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | (maintenance_head ite; first | apply lifted_conditional | apply conditional)
    | (maintenance_intro; try dsimp only; try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite])
    | split

theorem insertAllowedIpPrefix_preserves_product (c : ProductAmbientContracts I)
    (hc : ProductNodeAllocationStable I) (family addr cidr : Nat) (peer : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (insertAllowedIpPrefix family addr cidr peer)) := by
  simp only [insertAllowedIpPrefix, liftWGObserver_bind, apply_ite]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop
    (nodeAllocationLift_native_product c hc (fun _ => True) _ ?_))
  · intro _
    split
    · exact addAllowedIpPrefix_preserves_product c hc .root4 32 addr cidr (some peer)
    · exact addAllowedIpPrefix_preserves_product c hc .root6 128 addr cidr (some peer)
  · apply SameView.of_wp
    intro initial
    exact modifyDev_nodeAllocation_spec (fun t => t = initial) _ (fun _ => rfl)

inductive AllowedIpsInsertCall where
  | add (root : Slot) (bits key cidr : Nat) (peer : Option PeerId)
  | insert (family addr cidr : Nat) (peer : PeerId)

namespace AllowedIpsInsertCall

def original : AllowedIpsInsertCall → WG.M Int
  | .add root bits key cidr peer => WG.add root bits key cidr peer
  | .insert family addr cidr peer => WG.insert family addr cidr peer

def observed : AllowedIpsInsertCall → MixedM Int
  | .add root bits key cidr peer => addAllowedIpPrefix root bits key cidr peer
  | .insert family addr cidr peer => insertAllowedIpPrefix family addr cidr peer

theorem erases (call : AllowedIpsInsertCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | add root bits key cidr peer => exact addAllowedIpPrefix_erases root bits key cidr peer
  | insert family addr cidr peer => exact insertAllowedIpPrefix_erases family addr cidr peer

theorem preserves_ambient (c : AmbientContracts I) (hc : NodeAllocationStable I)
    (call : AllowedIpsInsertCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | add root bits key cidr peer => exact addAllowedIpPrefix_preserves c hc root bits key cidr peer
  | insert family addr cidr peer => exact insertAllowedIpPrefix_preserves c hc family addr cidr peer

theorem preserves_product (c : ProductAmbientContracts I) (hc : ProductNodeAllocationStable I)
    (call : AllowedIpsInsertCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | add root bits key cidr peer => exact addAllowedIpPrefix_preserves_product c hc root bits key cidr peer
  | insert family addr cidr peer => exact insertAllowedIpPrefix_preserves_product c hc family addr cidr peer

theorem allocation (call : AllowedIpsInsertCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationNodeAllocationStable

end AllowedIpsInsertCall
end Leanux.Proofs.WG.Lifetimes
