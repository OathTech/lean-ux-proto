import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionStaging

/-! Actual staged-send transport keeps packet coverage, pending encryption
aliases and active or suspended TX service together. This is a native local
contract; initialized caller coverage is composed separately. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def Serving (locals : List TxLocalBatch) (crypt : List (List SkbId))
    (tx : List PeerId) (w : WGWorld) : Prop :=
  Obligations crypt tx w ∧ Covered locals crypt w

theorem Serving.stage_ready (before : Serving locals crypt tx w) : StageReady locals crypt tx w :=
  ⟨before.1,⟨StackOwnership.Allocated.bounded before.2.1.1,before.2.1.2.1⟩,before.2.1.2.2⟩

theorem serving_staged (pid : PeerId) : Preserves (Serving locals crypt tx) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact ⟨staged_service before.stage_ready pid a b run,
    (hoare_iff_run_ambient _ _ _).mp (TxCovered.Native.staged pid) w a () v b before.2 run⟩

theorem At.native {action : WG.M α}
    (service : ∀tx,Preserves (Serving locals crypt tx) action)
    (suspension : TxSuspension.Keeps action) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have native:=HolderPoll.native_receipt run
  have after:Serving locals crypt (active++actors w.ambient.suspended) v.wg :=
    (hoare_iff_run_ambient _ _ _).mp (service _) w.wg w.ambient result v.wg v.ambient before native
  have same:=TxSuspension.native suspension native
  simpa only [At,Serving,same] using after

theorem staged_actor (pid : PeerId) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG (sendStagedPackets pid)) :=
  At.native (fun _=>serving_staged pid) (TxSuspension.staged pid)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
