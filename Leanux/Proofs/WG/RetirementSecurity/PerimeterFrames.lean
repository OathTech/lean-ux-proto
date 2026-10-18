import Leanux.Proofs.WG.RetirementSecurity.SlotProjection
import Leanux.Proofs.WG.RetirementSecurity.Confirmation
import Leanux.Proofs.WG.RetirementSecurity.Rotation

/-! Slot rotations change only their selected peer and key-reference state;
all other peer records and all packet cells remain available for the concrete
holder projection's boundary reassembly. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

def holderPerimeter (pid : PeerId) (w : WGWorld) :=
  ((fun other : PeerId => if other = pid then none
    else (peersAt w).bind fun peers => peers[other]?), (carrierShape w).2)

theorem put_perimeter (pid : PeerId) (key : Option KeypairId) (now : Bool) :
    SameView (holderPerimeter pid) (keypairPut key now) :=
  (put_carriers key now).factor fun shape =>
    ((fun other => if other = pid then none else shape.1.bind fun peers => peers[other]?),shape.2)

theorem setPeer_perimeter (pid : PeerId) (p : Peer) :
    SameView (holderPerimeter pid) (setPeer pid p) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  cases device : w.dev with
  | none => simp [holderPerimeter,carrierShape,peersAt,device]
  | some d =>
    apply Prod.ext
    · funext other
      by_cases same : other = pid
      · simp [holderPerimeter,same]
      · simp [holderPerimeter,peersAt,device,Std.TreeMap.getElem?_insert,same,Ne.symm same]
    · simp [holderPerimeter,carrierShape,device]

theorem getPeer_perimeter (pid selected : PeerId) :
    SameView (holderPerimeter pid) (getPeer selected) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  rw [(Origins.getPeer_return selected w v p a b run).1]

theorem getKeypair_perimeter (pid : PeerId) (key : KeypairId) :
    SameView (holderPerimeter pid) (getKeypair key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a k v b run
  rw [(KeyTimes.getKeypair_return key w v k a b run).1]

theorem updatePeer_perimeter (pid : PeerId) (f : Peer → Peer) :
    SameView (holderPerimeter pid) (updatePeer pid f) :=
  (getPeer_perimeter pid pid).bind (fun p => setPeer_perimeter pid (f p))

theorem confirmation_perimeter (pid : PeerId) (key : KeypairId) :
    SameView (holderPerimeter pid) (receivedWithKeypair pid key) := by
  intro initial
  let P : WGWorld → Prop := fun w => holderPerimeter pid w = initial
  change Preserves P (receivedWithKeypair pid key)
  unfold receivedWithKeypair
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact (getPeer_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head setPeer; exact (setPeer_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head keypairPut; exact (put_perimeter pid _ _).wp (fun view => view = initial))
    | (index_material_head modifyPeer; exact (updatePeer_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

theorem rotation_perimeter (pid : PeerId) (key : KeypairId) :
    SameView (holderPerimeter pid) (addNewKeypair pid key) := by
  intro initial
  let P : WGWorld → Prop := fun w => holderPerimeter pid w = initial
  change Preserves P (addNewKeypair pid key)
  unfold addNewKeypair
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact (getPeer_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head getKeypair; exact (getKeypair_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head setPeer; exact (setPeer_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head keypairPut; exact (put_perimeter pid _ _).wp (fun view => view = initial))
    | (index_material_head modifyPeer; exact (updatePeer_perimeter pid _).wp (fun view => view = initial))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

theorem perimeter_peer_order (before : w.dev = some d) (after : v.dev = some e)
    (found : peerAt v pid = some q)
    (perimeter : holderPerimeter pid v = holderPerimeter pid w) :
    e.peers.toList.Perm ((pid,q) :: d.peers.toList.filter
      (fun pair => decide (¬ (pid == pair.1)))) := by
  have equivalent : e.peers.Equiv (d.peers.insert pid q) := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro other
    by_cases same : other = pid
    · subst other
      have selected : e.peers[pid]? = some q := by simpa [peerAt,after] using found
      simp [selected]
    · have unchanged := congrFun (congrArg (fun view => view.1) perimeter) other
      simpa [holderPerimeter,peersAt,before,after,same,
        Std.TreeMap.getElem?_insert,Ne.symm same] using unchanged
  rw [equivalent.toList_eq]
  exact Std.TreeMap.toList_insert_perm

end Leanux.Proofs.WG.RetirementSecurity
