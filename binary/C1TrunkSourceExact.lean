import C1TrunkRootBody
import AllowedipsExactSource
import AllowedipsExactTotal
/-! Result C1, package 2: the source side of case `exact`. `step`'s device
for the case is the landed endpoint `Model.exactInstalled` (the device the
mirror's `Exact.assignment` produces), as plain equality: no invariant on
the ownership lists is needed. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- `C1Step.delete`'s fold changes only the peers, by the landed `delFold`. -/
theorem delete_fold (id : Nat) (xs : List (Nat × Peer)) (D : Device) :
    xs.foldl (fun d (x : Nat × Peer) => if x.2.allowedipsList.contains id then
      {d with peers := d.peers.insert x.1 {x.2 with allowedipsList := listRemove x.2.allowedipsList id}}
      else d) D = {D with peers := Model.delFold id xs D.peers} := by
  induction xs generalizing D with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [Model.delFold, List.foldl_cons, Model.delStep, Model.unlist]
    split <;> rfl

theorem delete_eq (D : Device) (id : Nat) :
    Proof.delete D id = {D with peers := (Model.unlisted D id).peers} := by
  unfold Proof.delete
  exact delete_fold id D.peers.toList D

/-- `step`'s device for case `exact` is the landed `exactInstalled`. -/
theorem exact_device (d0 : Device) (id pid : Nat) (n : AipNode) (owner : Peer)
    (hasPeer : d0.peers.get? pid = some owner) :
    addTail (Proof.delete {d0 with nodes := d0.nodes.insert id {n with peer := some pid}} id) pid id =
      Model.exactInstalled d0 id n pid owner := by
  rw [delete_eq]
  have hp : d0.peers[pid]? = some owner := hasPeer
  have got : (Model.unlisted {d0 with nodes := d0.nodes.insert id {n with peer := some pid}} id).peers.get? pid =
      some (Model.unlist id owner) := by
    show (Model.unlisted _ id).peers[pid]? = _
    rw [Model.unlisted_get]
    simp [hp]
  simp only [addTail, got]
  rfl

/-- The device the mirror's `Exact.assignment` leaves is `step`'s, up to
`Allowedips.target` (in fact equal). -/
theorem exact_run_device (k finalWG : WGWorld) (d0 finalDevice : Device) (ambient finalAmbient : Ambient)
    (id pid : Nat) (n : AipNode) (owner : Peer)
    (hasDevice : k.dev = some d0) (hasNode : d0.nodes.get? id = some n)
    (hasPeer : d0.peers.get? pid = some owner)
    (run : ((Exact.assignment id pid).run k).run ambient = .ok (((),finalWG),finalAmbient))
    (final : finalWG.dev = some finalDevice) :
    finalDevice =
      addTail (Proof.delete {d0 with nodes := d0.nodes.insert id {n with peer := some pid}} id) pid id := by
  obtain ⟨fa,run'⟩ := Exact.assignment_run k d0 ambient id pid n owner hasDevice hasNode hasPeer
  rw [run'] at run
  have same : ({k with dev := some (Model.exactInstalled d0 id n pid owner)} : WGWorld) = finalWG := by
    injection run with h
    exact congrArg (fun x => x.1.2) h
  rw [← same] at final
  rw [exact_device d0 id pid n owner hasPeer]
  exact (Option.some.inj final).symm

#print axioms delete_eq
#print axioms exact_device
#print axioms exact_run_device
end C1Trunk
