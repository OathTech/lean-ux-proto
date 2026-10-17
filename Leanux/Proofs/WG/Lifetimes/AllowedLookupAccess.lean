import Leanux.Proofs.WG.Lifetimes.MaintenanceCalls
import Leanux.Proofs.Framing.WGAllowedIps

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Allowed-IP lookups observe peer reference acquisition after the original
node search. Node and scalar accesses are outside the three lifetime stores.
No represented-trie or successful-search premise is imposed. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem swapEndian_sameWGStore (bits : Nat) : SameWGStore (swapEndian bits) := by
  intro initial
  let P := fun w : WGWorld => wgStoreView w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  change Preserves P (swapEndian bits)
  unfold swapEndian
  simp only [branch]
  repeat' first
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem findNode_sameAipStore (root : Option NodeId) (bits key : Nat) :
    SameView (fun s : AipStore => s) (findNode root bits key) := by
  intro initial
  let P := fun s : AipStore => s = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : AipM α) := hoare_liftAmbient a P
  have node (id : NodeId) : Preserves P (getNode id) :=
    (getNode_sameAipStore id).wp (fun s => s = initial)
  have loop {α β : Type} (xs : List α) (b : β) (f : α → β → AipM (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs b f) :=
    list_view_spec id P xs b f hf
  change Preserves P (findNode root bits key)
  unfold findNode prefixMatches commonBits choose AipNode.bitAt
  simp only [branch, invariant]
  repeat' first
    | (allocation_release_head getNode; exact node _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_head ForIn.forIn; first
        | apply loop
        | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
    | allocation_release_step

private theorem lookup_readAip {a : AipM α} (ha : SameView (fun s : AipStore => s) a) :
    SameWGStore (liftAip a) := by
  intro initial
  apply hoare_liftAip_of a (fun w => wgStoreView w = initial) (fun _ w => wgStoreView w = initial)
  intro g d hg hd
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro s ambient x s' ambient' hs hr
  have he := (ProjectedAction.iff_run_ambient _ _ _).mp ha s ambient x s' ambient' hr
  rw [he, hs]
  simpa [wgStoreView, hd] using hg

def lookupPrefix (root : Option NodeId) (bits key : Nat) : MixedM (Option PeerId) := do
  liftWGPrefix (swapEndian bits)
  let node ← liftWGPrefix (liftAip (findNode root bits key))
  if ← liftWGPrefix (branch .lookupFound node.isSome) then
    let some id := node | liftWGPrefix (invariant "unreachable")
    let peer ← peerGetMaybeZeroPrefix (← liftWGPrefix (liftAip (getNode id))).peer
    if ← liftWGPrefix (branch .lookupPeerGone peer.isNone) then
      liftWGPrefix (unsupported "lookup retry after a dying peer")
    return peer
  return none

def lookupSrcPrefix (protocol : Nat) (bytes : List UInt8) : MixedM (Option PeerId) := do
  let t := (← liftWGPrefix getDev).peerAllowedips
  if ← liftWGPrefix (branch .lookupSrcV4 (protocol == 4)) then return ← lookupPrefix t.root4 32 (beAt bytes 12 4)
  if ← liftWGPrefix (branch .lookupSrcV6 (protocol == 6)) then return ← lookupPrefix t.root6 128 (beAt bytes 8 16)
  return none

def lookupDstPrefix (family addr : Nat) : MixedM (Option PeerId) := do
  let t := (← liftWGPrefix getDev).peerAllowedips
  if ← liftWGPrefix (branch .lookupDstV4 (family == 4)) then return ← lookupPrefix t.root4 32 addr
  if ← liftWGPrefix (branch .lookupDstV6 (family == 6)) then return ← lookupPrefix t.root6 128 addr
  return none

theorem lookupPrefix_erases (root : Option NodeId) (bits key : Nat) :
    ErasesStatePrefix (lookupPrefix root bits key) (lookup root bits key) := by
  unfold lookupPrefix lookup
  repeat' first
    | with_reducible exact peerGetMaybeZeroPrefix_erases _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | split
    | (solve | simp_all)
    | (with_reducible intro x; try dsimp only)

  all_goals try simp_all only [Option.some.injEq]
  all_goals exact erasesStatePrefix_lift _

theorem lookupPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (root : Option NodeId) (bits key : Nat) :
    AmbientSpec I P (lookupPrefix root bits key) (fun _ => P) := by
  unfold lookupPrefix
  repeat' first
    | (maintenance_head peerGetMaybeZeroPrefix; exact peerGetMaybeZeroPrefix_spec_ambient c P _)
    | (maintenance_lift_action_head swapEndian; exact c.store P _ (swapEndian_sameWGStore _))
    | (maintenance_lift_action_head liftAip; exact c.store P _ (lookup_readAip (findNode_sameAipStore _ _ _)))
    | (maintenance_lift_action_head liftAip; exact c.store P _ (lookup_readAip (getNode_sameAipStore _)))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head invariant; exact c.invariant P _)
    | (maintenance_lift_action_head unsupported; exact c.store P _ (by intro initial; exact hoare_liftAmbient (AmbientM.unsupported _) _))
    | exact c.pure P _
    | apply StatePrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem lookupSrcPrefix_erases (protocol : Nat) (bytes : List UInt8) :
    ErasesStatePrefix (lookupSrcPrefix protocol bytes) (lookupSrc protocol bytes) := by
  unfold lookupSrcPrefix lookupSrc
  repeat' first
    | exact lookupPrefix_erases _ _ _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | split
    | (intro x; try dsimp only)

theorem lookupSrcPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (protocol : Nat) (bytes : List UInt8) : AmbientSpec I P (lookupSrcPrefix protocol bytes) (fun _ => P) := by
  unfold lookupSrcPrefix
  repeat' first
    | (maintenance_head lookupPrefix; exact lookupPrefix_spec c P _ _ _)
    | (maintenance_lift_action_head getDev; exact c.store P _ getDev_sameWGStore)
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | exact c.pure P _
    | apply StatePrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem lookupDstPrefix_erases (family addr : Nat) :
    ErasesStatePrefix (lookupDstPrefix family addr) (lookupDst family addr) := by
  unfold lookupDstPrefix lookupDst
  repeat' first
    | exact lookupPrefix_erases _ _ _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | split
    | (intro x; try dsimp only)

theorem lookupDstPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (family addr : Nat) : AmbientSpec I P (lookupDstPrefix family addr) (fun _ => P) := by
  unfold lookupDstPrefix
  repeat' first
    | (maintenance_head lookupPrefix; exact lookupPrefix_spec c P _ _ _)
    | (maintenance_lift_action_head getDev; exact c.store P _ getDev_sameWGStore)
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | exact c.pure P _
    | apply StatePrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem lookupPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (root : Option NodeId) (bits key : Nat) :
    ProductAmbientSpec I P (liftWGObserver (lookupPrefix root bits key)) (fun _ => P) := by
  have branch_spec (Q : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I Q (liftWGObserver (liftWGPrefix (Leanux.branch d b))) (fun _ => Q) :=
    c.nativeStore Q _ (by intro initial; exact hoare_liftAmbient (AmbientM.branch d b) _)
  have invariant_spec {α : Type} (Q : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I Q (liftWGObserver (liftWGPrefix (Leanux.invariant (α := α) why))) (fun _ => Q) :=
    c.nativeStore Q _ (by intro initial; exact hoare_liftAmbient (AmbientM.invariant why) _)
  unfold lookupPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  repeat' first
    | simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
    | (maintenance_head peerGetMaybeZeroPrefix; exact peerGetMaybeZeroPrefix_spec_product c P _)
    | (maintenance_lift_action_head swapEndian; exact c.nativeStore P _ (swapEndian_sameWGStore _))
    | (maintenance_lift_action_head liftAip; exact c.nativeStore P _ (lookup_readAip (findNode_sameAipStore _ _ _)))
    | (maintenance_lift_action_head liftAip; exact c.nativeStore P _ (lookup_readAip (getNode_sameAipStore _)))
    | (maintenance_lift_action_head branch; exact branch_spec P _ _)
    | (maintenance_lift_action_head invariant; exact invariant_spec P _)
    | (maintenance_lift_action_head unsupported; exact c.nativeStore P _ (by intro initial; exact hoare_liftAmbient (AmbientM.unsupported _) _))
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem lookupSrcPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (protocol : Nat) (bytes : List UInt8) : ProductAmbientSpec I P (liftWGObserver (lookupSrcPrefix protocol bytes)) (fun _ => P) := by
  have branch_spec (Q : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I Q (liftWGObserver (liftWGPrefix (Leanux.branch d b))) (fun _ => Q) :=
    c.nativeStore Q _ (by intro initial; exact hoare_liftAmbient (AmbientM.branch d b) _)
  have invariant_spec {α : Type} (Q : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I Q (liftWGObserver (liftWGPrefix (Leanux.invariant (α := α) why))) (fun _ => Q) :=
    c.nativeStore Q _ (by intro initial; exact hoare_liftAmbient (AmbientM.invariant why) _)
  unfold lookupSrcPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  repeat' first
    | simp only []
    | (maintenance_head lookupPrefix; exact lookupPrefix_spec_product c P _ _ _)
    | (maintenance_lift_action_head getDev; exact c.nativeStore P _ getDev_sameWGStore)
    | (maintenance_lift_action_head branch; exact branch_spec P _ _)
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem lookupDstPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (family addr : Nat) : ProductAmbientSpec I P (liftWGObserver (lookupDstPrefix family addr)) (fun _ => P) := by
  have branch_spec (Q : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I Q (liftWGObserver (liftWGPrefix (Leanux.branch d b))) (fun _ => Q) :=
    c.nativeStore Q _ (by intro initial; exact hoare_liftAmbient (AmbientM.branch d b) _)
  have invariant_spec {α : Type} (Q : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I Q (liftWGObserver (liftWGPrefix (Leanux.invariant (α := α) why))) (fun _ => Q) :=
    c.nativeStore Q _ (by intro initial; exact hoare_liftAmbient (AmbientM.invariant why) _)
  unfold lookupDstPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  repeat' first
    | simp only []
    | (maintenance_head lookupPrefix; exact lookupPrefix_spec_product c P _ _ _)
    | (maintenance_lift_action_head getDev; exact c.nativeStore P _ getDev_sameWGStore)
    | (maintenance_lift_action_head branch; exact branch_spec P _ _)
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
