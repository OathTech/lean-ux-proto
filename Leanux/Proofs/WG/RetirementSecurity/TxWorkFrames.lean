import Leanux.Proofs.WG.RetirementSecurity.TxCryptAdmission

/-! Frames for the actual pending TX work queue. Ring entries and peer
packet queues remain separate obligations; this projection records only work
that the scheduler has not yet dispatched. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def queued (w : WGWorld) : List PeerId := (w.dev.map (·.txWorkQueue)).getD []

theorem store {action : WG.M α} (frame : SameWGStore action) : SameView queued action :=
  frame.of_factor (fun s : WGStoreView=>(s.dev.map (·.txWorkQueue)).getD []) _ (fun _=>rfl)

theorem modify (f : Device→Device) (same : ∀d,(f d).txWorkQueue=d.txWorkQueue) :
    SameView queued (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  simp [queued,Option.map_map,Function.comp_def,same]

theorem peer_put (peer : Option PeerId) : SameView queued (peerPut peer) := by
  intro initial
  let P := fun w : WGWorld=>queued w=initial
  have ambient {α : Type} (action : AmbientM α) :
      Preserves P (monadLift action : WG.M α) := hoare_liftAmbient action P
  have index {α : Type} (action : IndexM α) :
      Preserves P (monadLift action : WG.M α) := by
    apply hoare_liftIndex action
    intro w d table before device
    simpa [P,queued,device] using before
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h=>h) (fun _ _ h=>h.2)
  have write (f : Device→Device) (same : ∀d,(f d).txWorkQueue=d.txWorkQueue) :
      Preserves P (modifyDev f) := (modify f same).wp (·=initial)
  change Preserves P _
  unfold peerPut getPeer getDev setPeer
  simp only [branch,branchCmp,refcountDecAndTest,invariant,unsupported,
    requireNotPending,retirePeerUnits,modifyAmbient]
  repeat' first
    | (allocation_release_head modifyDev; apply write; intro; rfl)
    | (allocation_release_lift_from IndexM; exact index _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step
  all_goals first
    | exact read
    | (apply hoare_modify; intro w h; exact h)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
