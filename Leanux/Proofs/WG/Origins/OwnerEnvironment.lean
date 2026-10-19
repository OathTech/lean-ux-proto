import Leanux.Proofs.WG.Origins.OwnerHandshake
import Leanux.Proofs.WG.Origins.OwnerTransmit
import Leanux.Proofs.WG.Origins.OwnerCryptWorkers

/-! Receiving-owner checks through the actual scheduler observer. Worker calls
retain their committed journals; copied consistency trials contribute only the
existing filter marker. All recorded failures retain their actual prefix. -/
namespace Leanux.Proofs.WG.OwnerEnvironment
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits Origins CurrentEnvironment
open Origins.HistorySupport (sensitive)

private theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) :
    OwnerChecks.Preserves (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.safe) OwnerWorkers.store frame

private theorem mixed_store (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (allocation : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe g)
    (frame : SameProductStore a) : OwnerChecks.Preserves (RxHistory.mixed g) := by
  apply OwnerChecks.quiet _ (Appends.focus _ _ _)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      sensitive (fun _ => rfl) _)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.mixed_store)
      g a erases frame)
    (RxHistory.mixed_preserves allocation)
  intro w h hi result v hr
  exact (hoare_iff_run _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEncrypt.«0».Leanux.Proofs.WG.OwnerEncrypt.product_store) a frame)
    w result v hi.carrier ((RxHistory.mixed_erases erases w h).symm.trans hr)

private theorem mixed_lift (a : Leanux.M α) (frame : SameProductStore a) :
    OwnerChecks.Preserves (RxHistory.mixed (liftPrefix a)) :=
  mixed_store _ _ (erasesPrefix_lift a)
    (ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store
      (fun _ => True) a frame)) frame

private theorem mixed_throw (e : Stop) :
    OwnerChecks.Preserves (RxHistory.mixed (throw e : PrefixM LifetimeEvent α)) :=
  mixed_store _ _ (erasesPrefix_throw e)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxActivationHistory.«0».Leanux.Proofs.WG.Queues.RxHistory.throw_allocation) e)
    (HistorySupport.source_throw _ e)

private theorem peer (pid : PeerId) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (getPeerMixed pid))) := by
  apply OwnerChecks.native_mixed _ _ (getPeerMixed_erases pid)
    (AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) pid))
    (Retaining.of_view (Retaining.getPeer_material pid))
  · exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentLifecycle.«0».Leanux.Proofs.WG.CurrentLifecycle.readPeer_preserves) pid
  · intro history
    exact hoare_consequence (OwnerControls.readPeer pid) (fun _ hi => hi.2) (fun _ _ hi => hi)

private theorem packet (id : SkbId) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (getTxSkbPrefix id))) := by
  have frame : SameWGStore (getTxSkb id) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient pkt v finalAmbient hr
    exact congrArg wgStoreView (Packets.getTxSkb_current id w v pkt ambient finalAmbient hr).1
  apply OwnerChecks.native_mixed _ _ (getTxSkbPrefix_erases id)
    (AmbientContracts.drop (allocationTx.get (fun _ => True) id))
    (Retaining.of_view (Origins.sameView_of_sameWG (project := fun w : WGWorld => w) frame))
  · intro history
    exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.native_store)
      _ frame history
  · intro history
    exact hoare_consequence (OwnerControls.store _ frame) (fun _ hi => hi.2) (fun _ _ hi => hi)

private theorem work (f : List PeerId → List PeerId) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver
      (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})))) := by
  apply OwnerChecks.native_mixed _ _ (erasesStatePrefix_lift _) (txWorkQueue_allocation f)
  · exact Retaining.of_view (Retaining.modifyDev_material _ (fun _ => rfl))
  · intro history
    exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentLifecycle.«0».Leanux.Proofs.WG.CurrentLifecycle.modifyDev_preserves)
      (fun d => {d with txWorkQueue := f d.txWorkQueue}) (fun _ => rfl) (fun _ => rfl) history
  · intro history
    apply hoare_consequence (OwnerControls.modifyDevice
      (fun d => {d with txWorkQueue := f d.txWorkQueue})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
      (fun _ hi => hi.2) (fun _ _ hi => hi)

private theorem occupancy (a : Activation) :
    OwnerChecks.Preserves (RxHistory.mixed (activationOccupancyPrefix a)) :=
  mixed_store _ _ (activationOccupancyPrefix_erases a)
    (activationOccupancyPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) a)
    (activationOccupancy_sameKernel a)

private theorem refills :
    OwnerChecks.Preserves (RxHistory.mixed activationRefillsPrefix) :=
  mixed_store _ _ activationRefillsPrefix_erases
    (activationRefillsPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient))
    activationRefills_sameKernel

private theorem hasWork (a : Activation) :
    OwnerChecks.Preserves (RxHistory.mixed (activationHasWorkPrefix a)) :=
  mixed_store _ _ (activationHasWorkPrefix_erases a)
    (activationHasWorkPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient)
      (ProductTxContracts.ofNative allocationTx) a)
    (activationHasWork_sameKernel a)

private theorem pending (next : Option Nat) :
    OwnerChecks.Preserves (RxHistory.mixed (pendingNapiPrefix next)) := by
  apply mixed_store _ _ (pendingNapiPrefix_erases next)
    (pendingNapiPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) next)
  unfold pendingNapi
  exact SameView.bind (liftWG_sameProductStore getDev getDev_sameWGStore) (fun _ => SameView.pure _ _)

open Lean Meta Elab Tactic in
elab "owner_env_outer " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``PrefixPreserves do throwError "not a prefix contract"
  let fields := target.getAppArgs
  unless fields.size > 0 do throwError "missing observer"
  let action := fields.back!.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  unless action.getAppFn.constName? == some expected do throwError "different outer observer"

macro "owner_env_steps" : tactic => `(tactic| first
  | (current_env_at HistoryAdapters.receiveIteration; exact OwnerHandshake.receiveIteration)
  | (current_env_at getPeerMixed; exact peer _)
  | (current_env_at getTxSkbPrefix; exact packet _)
  | (current_env_at activationRefillsPrefix; exact refills)
  | (current_env_at Env.pendingDevice; exact lift_store _ (pendingDevice_sameKernel _ _))
  | (current_env_at activationOccupancyPrefix; exact occupancy _)
  | (current_env_at activationHasWorkPrefix; exact hasWork _)
  | (current_env_at pendingNapiPrefix; exact pending _)
  | (current_env_at txIterPrefix; exact OwnerTransmit.txIteration _)
  | (current_env_at liftWGPrefix
     first
     | with_reducible exact work (fun q => q ++ [_])
     | with_reducible exact work (fun q => q.erase _))
  | (current_env_at getDev; exact lift_store _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  | (current_env_at liftPrefix
     first
     | (owner_env_outer RxHistory.mixed; apply mixed_lift)
     | (owner_env_outer liftPrefix; apply lift_store)
     simp only [getAmbient,hidden,peekHiddenSite,recordBudget,budgetExhausted,peekUnit,
       resolveUnit,modifyAmbient,invariant,unsupported]
     intro initial
     exact productAmbient_spec _ _ (fun _ _ hi => hi))
  | (current_env_at throw; exact mixed_throw _)
  | (current_env_at Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _)
  | (current_env_at ForIn.forIn; first
      | apply PrefixPreserves.range (State := World) _ _ _ (fun _ _ hi => hi.safe)
      | apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe))
  | (current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (current_env_at ite; split)
  | current_env_match
  | support_intro)

theorem cryptAhead (pid : PeerId) : OwnerChecks.Preserves (RxHistory.cryptAhead pid) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold RxHistory.cryptAhead
  repeat' first
    | (current_env_at RxHistory.encryptIteration; exact OwnerEncrypt.encryptIteration)
    | owner_env_steps

theorem activationIteration (a : Activation) : OwnerChecks.Preserves (RxHistory.activationIteration a) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold RxHistory.activationIteration
  repeat' first
    | (current_env_at RxHistory.encryptIteration; exact OwnerEncrypt.encryptIteration)
    | (current_env_at RxHistory.decryptIteration; exact OwnerCryptWorkers.decryptIteration)
    | (current_env_at RxHistory.cryptAhead; exact cryptAhead _)
    | owner_env_steps

theorem activationRun (a : Activation) : OwnerChecks.Preserves (RxHistory.activationRun a) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold RxHistory.activationRun
  repeat' first
    | (current_env_at RxHistory.activationIteration; exact activationIteration _)
    | owner_env_steps

theorem dispatch (worker : Worker) : OwnerChecks.Preserves (RxHistory.dispatch worker) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold RxHistory.dispatch
  repeat' first
    | (current_env_at RxHistory.activationRun; exact activationRun _)
    | owner_env_steps

theorem schedule (stack : Option Worker) : OwnerChecks.Preserves (RxHistory.schedule stack) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold RxHistory.schedule
  simp only [List.find?_cons,List.find?_nil]
  repeat' first
    | (current_env_at RxHistory.dispatch; exact dispatch _)
    | (current_env_at RxHistory.activationRun; exact activationRun _)
    | (current_env_at RxHistory.napiSoftirq; exact OwnerWorkers.napiSoftirq)
    | (current_env_at RxHistory.audit; exact OwnerChecks.filter_probe)
    | owner_env_steps

theorem nestedResched (self : Worker) : OwnerChecks.Preserves (RxHistory.nestedResched self) := by
  unfold RxHistory.nestedResched
  apply PrefixPreserves.bind (lift_store _ (condResched_sameKernel _))
  intro b
  split
  · exact schedule _
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _

end Leanux.Proofs.WG.OwnerEnvironment
