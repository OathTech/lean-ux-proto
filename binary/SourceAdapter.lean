import Leanux.WG.Device

/-! Execution of the current split mirror through its actual product-world
adapters. These abbreviations contain no operational reimplementation. -/
namespace Leanux.World
/- Read-only projections used by the older history proofs. State is stored only
in the current World components; there is no duplicate or legacy state. -/
@[simp] abbrev steps (w : World) := w.ambient.steps
abbrev hidden (w : World) := w.ambient.hidden
@[simp] abbrev netRxSection (w : World) := w.ambient.netRxSection
@[simp] abbrev netRxSections (w : World) := w.ambient.netRxSections
abbrev envCalls (w : World) := w.ambient.envCalls
abbrev suspended (w : World) := w.ambient.suspended
abbrev pendingWork (w : World) := w.ambient.pendingWork
abbrev env (w : World) := w.ambient.env
abbrev timing (w : World) := w.ambient.timing
abbrev hiddenPlaceholders (w : World) := w.ambient.hiddenPlaceholders
abbrev netRxRaised (w : World) := w.wg.netRxRaised
abbrev userFds (w : World) := w.fs.userFds
end Leanux.World

namespace Binary
abbrev M := Leanux.M
namespace Source
open Leanux Leanux.WG

abbrev getWG : Leanux.M WGWorld := liftWG (get : WG.M WGWorld)
abbrev modifyWG (f : WGWorld → WGWorld) : Leanux.M Unit := liftWG (modify f)

abbrev getDev : Leanux.M Device := liftWG WG.getDev
abbrev modifyDev (f : Device → Device) : Leanux.M Unit := liftWG (WG.modifyDev f)
abbrev getPeer (id : PeerId) : Leanux.M Peer := liftWG (WG.getPeer id)
abbrev setPeer (id : PeerId) (p : Peer) : Leanux.M Unit := liftWG (WG.setPeer id p)
abbrev getKeypair (id : KeypairId) : Leanux.M Keypair := liftWG (WG.getKeypair id)
abbrev setKeypair (id : KeypairId) (p : Keypair) : Leanux.M Unit := liftWG (WG.setKeypair id p)
abbrev getNode (id : NodeId) : Leanux.M AipNode := liftWG (liftAip (WG.getNode id))
abbrev requireNotPending (id : PeerId) (what : String) : Leanux.M Unit :=
  liftWG (WG.requireNotPending id what)
abbrev peerWord (owner : IndexOwner) : Leanux.M (Option PeerId) := liftWG owner.peerWord
abbrev setPeerWord (owner : IndexOwner) (peer : Option PeerId) : Leanux.M Unit :=
  liftWG (owner.setPeerWord peer)
abbrev peerGetMaybeZero (peer : Option PeerId) : Leanux.M (Option PeerId) :=
  liftWG (WG.peerGetMaybeZero peer)
abbrev indexBucket (index : Nat) : Leanux.M (List IndexEntry) := liftWG (liftIndex (WG.indexBucket index))
abbrev indexHashed (owner : IndexOwner) : Leanux.M Bool := liftWG (liftIndex (WG.indexHashed owner))
abbrev indexRemove (owner : IndexOwner) : Leanux.M Unit := liftWG (liftIndex (WG.indexRemove owner))
abbrev indexReplaceHandshake (pid : PeerId) (kid : KeypairId) : Leanux.M Bool :=
  liftWG (liftIndex (WG.indexReplaceHandshake pid kid))
abbrev indexInsert (owner : IndexOwner) : Leanux.M Nat := liftWG (liftIndex (WG.indexInsert owner))
abbrev indexLookup (kinds : List IndexKind) (index : Nat) : Leanux.M (Option (IndexOwner × PeerId)) :=
  liftWG (WG.indexLookup kinds index)
abbrev swapEndian (bits : Nat) : Leanux.M Unit := liftWG (WG.swapEndian bits)
abbrev findNode (root : Option NodeId) (bits key : Nat) : Leanux.M (Option NodeId) :=
  liftWG (liftAip (WG.findNode root bits key))
abbrev lookup (root : Option NodeId) (bits key : Nat) : Leanux.M (Option PeerId) :=
  liftWG (WG.lookup root bits key)

theorem bind_congr_right (m : Leanux.M α) (f g : α → Leanux.M β)
    (h : ∀ a, f a = g a) : (m >>= f) = (m >>= g) := congrArg (m >>= ·) (funext h)

@[simp] theorem liftWG_pure (a : α) : liftWG (pure a) = (pure a : Leanux.M α) := rfl
@[simp] theorem liftWG_bind (a : WG.M α) (f : α → WG.M β) :
    liftWG (a >>= f) = (liftWG a >>= fun v => liftWG (f v)) := by
  funext w
  change (liftWG (a >>= f)).run w = ((liftWG a >>= fun v => liftWG (f v))).run w
  simp only [StateT.run, liftWG, bind, StateT.bind]
  cases h : a w.wg w.ambient with
  | error e => rfl
  | ok out =>
    rcases out with ⟨⟨v, wg⟩, ambient⟩
    cases f v wg ambient <;> rfl

@[simp] theorem branch_run (d : Decision) (b : Bool) (w : World) :
    (branch d b : Leanux.M Bool).run w = .ok (b,
      {w with ambient := {w.ambient with steps := w.ambient.steps.push {decision := d, outcome := b, netRx := w.ambient.netRxSection}}}) := rfl

@[simp] theorem branchCmp_run (d : Decision) (b : Bool) (a c : Int) (w : World) :
    (branchCmp d b a c : Leanux.M Bool).run w = .ok (b,
      {w with ambient := {w.ambient with steps := w.ambient.steps.push {decision := d, outcome := b, operands := some (a, c), netRx := w.ambient.netRxSection}}}) := rfl

@[simp] theorem unsupported_run (message : String) (w : World) :
    (unsupported message : Leanux.M α).run w = .error (.outsideDomain
      (match w.ambient.steps.back? with
       | some s => s!"{s.decision.info.file}:{s.decision.info.line}"
       | none => "syscall entry") message) := rfl

@[simp] theorem liftWG_branch (d : Decision) (b : Bool) :
    liftWG (branch d b) = (branch d b : Leanux.M Bool) := rfl

@[simp] theorem liftWG_branchCmp (d : Decision) (b : Bool) (a c : Int) :
    liftWG (branchCmp d b a c) = (branchCmp d b a c : Leanux.M Bool) := rfl

@[simp] theorem liftWG_unsupported (message : String) :
    liftWG (unsupported message : WG.M α) = (unsupported message : Leanux.M α) := rfl

@[simp] theorem liftWG_refcountIncNotZero (old : Nat) :
    liftWG (refcountIncNotZero old) = (refcountIncNotZero old : Leanux.M Bool) := by
  simp only [refcountIncNotZero, liftWG_bind, liftWG_pure, liftWG_branch,
    liftWG_branchCmp, liftWG_unsupported, apply_ite]

@[simp] theorem liftWG_forIn (xs : List α) (a : β) (f : α → β → WG.M (ForInStep β)) :
    liftWG (forIn xs a f) = forIn xs a (fun x b => liftWG (f x b)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, liftWG_bind]
    congr 1
    funext result
    cases result <;> simp only [liftWG_pure, ih]

@[simp] theorem except_ok_bind (a : α) (f : α → Except Stop β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] theorem except_pure (a : α) : (pure a : Except Stop α) = .ok a := rfl
@[simp] theorem liftWG_option (o : Option α) (n : WG.M β) (s : α → WG.M β) :
    liftWG (match o with | none => n | some v => s v) =
      (match o with | none => liftWG n | some v => liftWG (s v)) := by cases o <;> rfl
@[simp] theorem liftWG_invariant (message : String) :
    liftWG (invariant message : WG.M α) = (invariant message : Leanux.M α) := rfl
@[simp] theorem liftWG_map (f : α → β) (a : WG.M α) :
    liftWG (f <$> a) = f <$> liftWG a := by
  simp only [map_eq_pure_bind, liftWG_bind, liftWG_pure]

@[simp] theorem liftWG_option_some (o : Option α) (n : WG.M β) (s : α → WG.M β) :
    liftWG (match o with | some v => s v | _ => n) =
      (match o with | some v => liftWG (s v) | _ => liftWG n) := by cases o <;> rfl

@[simp] theorem lookup_return_lift (owner : IndexOwner) (peer : Option PeerId) :
    liftWG (do
      let some pid := peer | invariant "unreachable"
      return some (owner, pid)) =
    (do
      let some pid := peer | invariant "unreachable"
      return some (owner, pid) : Leanux.M (Option (IndexOwner × PeerId))) := by
  cases peer <;> rfl

end Source
end Binary
