import Leanux.Proofs.WG.RetirementSecurity.HolderTransport
import Leanux.Proofs.WG.RetirementSecurity.PacketPayments
import Leanux.Proofs.WG.Queues.TxDisposal

/-! Native acquisition and release do not move physical holders. Their
refcount changes are deliberately absent from this carrier projection. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem put_carriers (kp : Option KeypairId) (now : Bool) :
    SameView carrierShape (keypairPut kp now) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  have peers := put_peers kp now w v a b run
  have tx := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Queues.TxDisposition.keyPut_packets kp now) w a () v b run
  have rx := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Queues.RxCredits.keypairPut_credit_frame kp now) w a () v b run
  have rxPackets := congrArg (fun p => p.2.2) rx
  exact Prod.ext peers (Prod.ext tx rxPackets)

theorem get_carriers (kp : Option KeypairId) :
    SameView carrierShape (keypairGet kp) := by
  intro initial
  let P : WGWorld → Prop := fun w => carrierShape w = initial
  have getter (id : KeypairId) : Preserves P (getKeypair id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b hi run
    exact (KeyTimes.getKeypair_return id w v k a b run).1 ▸ hi
  have setter (id : KeypairId) (k : Keypair) : Preserves P (setKeypair id k) := by
    unfold setKeypair modifyDev
    apply hoare_modify
    intro w hi
    cases device : w.dev <;> simpa [P,carrierShape,peersAt,device] using hi
  change Preserves P (keypairGet kp)
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,unsupported,invariant]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter _)
    | (index_material_head setKeypair; exact setter _ _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match
    | contradiction

end Leanux.Proofs.WG.RetirementSecurity
