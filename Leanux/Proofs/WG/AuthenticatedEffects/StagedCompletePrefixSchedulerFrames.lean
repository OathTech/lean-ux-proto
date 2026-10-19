import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProductSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSchedulerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedFrames

/-! Scheduler bookkeeping transports the existing native endpoint invariant
and all journal prefixes; these native lifts append no events. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem state_store (action : WG.M α) (frame : SameWGStore action) :
    StateChecked (liftWGPrefix action) :=
  StateEnsures.quiet (CompleteProduct.state_store action frame) (fun _ _ _=>rfl)

theorem append_work (pid : PeerId) :
    StateChecked (liftWGPrefix (modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue++[pid]})) :=
  StateEnsures.quiet (CompleteProduct.append_work pid) (fun _ _ _=>rfl)

theorem erase_work (pid : PeerId) :
    StateChecked (liftWGPrefix (modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid})) :=
  StateEnsures.quiet (CompleteProduct.erase_work pid) (fun _ _ _=>rfl)

theorem work_queue (f : List PeerId→List PeerId) :
    StateChecked (liftWGPrefix (modifyDev fun d=>{d with txWorkQueue:=f d.txWorkQueue})) :=
  StateEnsures.quiet (CompleteProduct.work_queue f) (fun _ _ _=>rfl)

theorem throw_checked (reason : Stop) : Checked (liftPrefix (throw reason : Leanux.M α)) :=
  native _ (CompleteProduct.throw_checked reason)

theorem resched (worker : Worker) (site : Decision) : Checked (Driver.reschedObserved worker site) := by
  unfold Driver.reschedObserved
  exact bind_checked (product_store _ (condResched_sameKernel worker))
    (fun yes=>ambient (AmbientM.branch site yes))

open Lean Meta Elab Tactic in
elab "prefix_product_wg " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Checked do throwError "not a paired product contract"
  let action := target.getAppArgs.back!.consumeMData
  unless action.isAppOf ``liftPrefix do throwError "not a product lift"
  let native := action.getAppArgs.back!.consumeMData
  unless native.isAppOf ``liftWG do throwError "not a WG lift"
  let .const actual _ := native.getAppArgs.back!.consumeMData.getAppFn | throwError "not a native source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different WG source"

macro "prefix_scheduler_native" : tactic => `(tactic| first
  | (prefix_product_wg modifyDev; first | exact wg _ (append_work _) | exact wg _ (erase_work _))
  | (prefix_product_wg getPeer; exact wg _ (state_store _ (CompleteProduct.peer_read_store _)))
  | (prefix_product_wg getTxSkb; exact wg _ (state_store _ (CompleteProduct.skb_read_store _)))
  | (prefix_product_wg getDev; exact wg _ (state_store _ getDev_sameWGStore))
  | (prefix_product_native getAmbient; exact ambient (get : AmbientM Ambient))
  | (prefix_product_native modifyAmbient; exact ambient _)
  | (prefix_product_native peekHiddenSite; exact ambient _)
  | (prefix_product_native invariant; exact ambient _)
  | (prefix_product_native throw; exact throw_checked _))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
