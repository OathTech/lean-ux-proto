import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedFrames

/-! Scheduler bookkeeping changes worker queues, not packet ownership or
allocation identities. Native frames keep those independent facts together. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem state_store (action : WG.M α) (frame : SameWGStore action) :
    StateChecked (liftWGPrefix action) :=
  pair (CompletePassive.native Safe account_safe action (TimerFrames.store frame))
    (erasesStatePrefix_lift action) (AllocatedFrames.store frame)

theorem peer_read_store (pid : PeerId) : SameWGStore (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  exact congrArg wgStoreView (getPeer_normal pid w v value a b run).1

theorem skb_read_store (id : SkbId) : SameWGStore (getTxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  exact congrArg wgStoreView (Packets.getTxSkb_current id w v value a b run).1

theorem work_queue (f : List PeerId → List PeerId) :
    StateChecked (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})) := by
  apply CompleteAllocated.native Safe account_safe
  intro h ledger
  apply hoare_modify
  intro w before
  refine ⟨before.1.same_view ?_,?_⟩
  · unfold StagedEntry.view
    apply Prod.ext
    · cases device : w.dev <;> simp [Packets.epoch,device]
    apply Prod.ext
    · funext id
      cases device : w.dev <;> simp [Staged.stagedAt,device]
    apply Prod.ext
    · funext id
      cases device : w.dev <;> simp [PacketMaterial.view,TxDisposition.txPackets,device]
    apply Prod.ext
    · cases device : w.dev <;> simp [Packets.snapshot,Packets.deviceStore,device]
    apply Prod.ext
    · funext id
      cases device : w.dev <;> simp [TxDisposition.txPackets,device]
    · funext id
      cases device : w.dev <;> simp [txQueueContents,RxCredits.handoffTxView,device]
  · obtain ⟨history,allocated⟩ := before.2
    refine ⟨history,allocated.congr ?_ ?_⟩
    · unfold identityView
      apply Prod.ext
      · cases device : w.dev <;> simp [Peers.snapshot,device]
      apply Prod.ext
      · funext id
        cases device : w.dev <;> simp [keypairResidents,device]
      · funext id
        cases device : w.dev <;> simp [packetResidents,device]
    · cases device : w.dev <;> simp [allocationMetadata,deviceAllocationMetadata,device]

theorem append_work (pid : PeerId) :
    StateChecked (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})) :=
  work_queue (· ++ [pid])

theorem erase_work (pid : PeerId) :
    StateChecked (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid})) :=
  work_queue (·.erase pid)

theorem throw_checked (reason : Stop) : Checked (liftPrefix (throw reason : Leanux.M α)) := by
  intro w h before
  exact ⟨[],by simp,carrier_safe h w before,True.intro⟩

theorem resched (worker : Worker) (site : Decision) : Checked (Driver.reschedObserved worker site) := by
  unfold Driver.reschedObserved
  exact bind_checked (product_store _ (condResched_sameKernel worker))
    (fun yes => ambient (AmbientM.branch site yes))

open Lean Meta Elab Tactic in
elab "complete_product_wg " wanted:ident : tactic => withMainContext do
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

macro "complete_scheduler_native" : tactic => `(tactic| first
  | (complete_product_wg modifyDev; first | exact wg _ (append_work _) | exact wg _ (erase_work _))
  | (complete_product_wg getPeer; exact wg _ (state_store _ (peer_read_store _)))
  | (complete_product_wg getTxSkb; exact wg _ (state_store _ (skb_read_store _)))
  | (complete_product_wg getDev; exact wg _ (state_store _ getDev_sameWGStore))
  | (complete_product_native getAmbient; exact ambient (get : AmbientM Ambient))
  | (complete_product_native modifyAmbient; exact ambient _)
  | (complete_product_native peekHiddenSite; exact ambient _)
  | (complete_product_native invariant; exact ambient _)
  | (complete_product_native throw; exact throw_checked _))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
