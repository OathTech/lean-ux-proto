import Leanux.Proofs.WG.Packets.PublicationTransmit
import Leanux.Proofs.WG.Packets.PublicationHandshakeObserved
import Leanux.Proofs.WG.Origins.OwnerEnvironment

/-! The actual scheduler composes owner evidence with packet certificates.
Copied consistency trials contribute their existing probe, not trial events. -/
namespace Leanux.Proofs.WG.PublicationJoint
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Origins CurrentEnvironment

theorem mixed_store (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (owner : OwnerChecks.Preserves (RxHistory.mixed g))
    (erases : ErasesPrefix g a) (frame : SameProductStore a) : Preserves (RxHistory.mixed g) :=
  mixed g a owner erases
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationFrontierPoll.«0».Leanux.Proofs.WG.PublicationFrontier.product_store)
      a frame)

private theorem mixed_lift (a : Leanux.M α) (frame : SameProductStore a) :
    Preserves (RxHistory.mixed (liftPrefix a)) :=
  mixed_store _ _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.mixed_lift) a frame)
    (erasesPrefix_lift a) frame

private theorem mixed_throw (e : Stop) :
    Preserves (RxHistory.mixed (throw e : PrefixM LifetimeEvent α)) :=
  mixed_store _ _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.mixed_throw) e)
    (erasesPrefix_throw e) (HistorySupport.source_throw _ e)

private theorem peer (pid : PeerId) :
    Preserves (RxHistory.mixed (liftWGObserver (getPeerMixed pid))) := by
  apply native_mixed _ (getPeer pid)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.peer) pid)
    (getPeerMixed_erases pid)
  intro history
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi hr
  exact (Queues.getPeer_normal pid w v p a b hr).1 ▸ hi

private theorem packet (id : SkbId) :
    Preserves (RxHistory.mixed (liftWGObserver (getTxSkbPrefix id))) := by
  apply native_mixed _ (getTxSkb id)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.packet) id)
    (getTxSkbPrefix_erases id)
  intro history
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi hr
  exact (Packets.getTxSkb_current id w v p a b hr).1 ▸ hi

private theorem work (f : List PeerId → List PeerId) :
    Preserves (RxHistory.mixed (liftWGObserver
      (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})))) :=
  native_mixed _ _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.work) f)
    (erasesStatePrefix_lift _)
    (PublicationFrontier.modifyDev_preserves _ (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ _ => rfl))

private theorem occupancy (a : Activation) :
    Preserves (RxHistory.mixed (activationOccupancyPrefix a)) :=
  mixed_store _ _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.occupancy) a)
    (activationOccupancyPrefix_erases a) (activationOccupancy_sameKernel a)

private theorem hasWork (a : Activation) :
    Preserves (RxHistory.mixed (activationHasWorkPrefix a)) :=
  mixed_store _ _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.hasWork) a)
    (activationHasWorkPrefix_erases a) (activationHasWork_sameKernel a)

private theorem pendingNapi (next : Option Nat) :
    Preserves (RxHistory.mixed (pendingNapiPrefix next)) := by
  apply mixed_store _ _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.pending) next)
    (pendingNapiPrefix_erases next)
  unfold Lifetimes.pendingNapi
  exact SameView.bind (liftWG_sameProductStore getDev getDev_sameWGStore) (fun _ => SameView.pure _ _)

/-- The real consistency filter changes no stored packet identity and appends
no consume. Its owner probe still captures the exact entry and strict prefix. -/
theorem filter_probe : Preserves (RxHistory.audit consistentFilterAudit) := by
  apply quiet _ _ OwnerChecks.filter_probe (Appends.focus _ _ _)
    (RxHistory.audit_erases consistentFilterAudit_erases)
  · exact focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent
      PublicationChecks.sensitive (fun _ => rfl) _
  · intro history
    apply (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationFrontierPoll.«0».Leanux.Proofs.WG.PublicationFrontier.product_store)
    apply SameView.bind
    · intro initial
      exact productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi)
    · intro ambient
      exact filterM_sameKernel productStoreView _ activationConsistent_sameKernel _

macro "publication_env_steps" : tactic => `(tactic| first
  | (current_env_at HistoryAdapters.receiveIteration; exact receiveIteration)
  | (current_env_at getPeerMixed; exact peer _)
  | (current_env_at getTxSkbPrefix; exact packet _)
  | (current_env_at activationOccupancyPrefix; exact occupancy _)
  | (current_env_at activationHasWorkPrefix; exact hasWork _)
  | (current_env_at pendingNapiPrefix; exact pendingNapi _)
  | (current_env_at txIterPrefix; exact txIteration _)
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

theorem cryptAhead (pid : PeerId) : Preserves (RxHistory.cryptAhead pid) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.cryptAhead
  repeat' first
    | (current_env_at RxHistory.encryptIteration; exact encryptIteration)
    | publication_env_steps

theorem activationIteration (a : Activation) : Preserves (RxHistory.activationIteration a) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.activationIteration
  repeat' first
    | (current_env_at RxHistory.encryptIteration; exact encryptIteration)
    | (current_env_at RxHistory.decryptIteration; exact decryptIteration)
    | (current_env_at RxHistory.cryptAhead; exact cryptAhead _)
    | publication_env_steps

theorem activationRun (a : Activation) : Preserves (RxHistory.activationRun a) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.activationRun
  repeat' first
    | (current_env_at RxHistory.activationIteration; exact activationIteration _)
    | publication_env_steps

theorem dispatch (worker : Worker) : Preserves (RxHistory.dispatch worker) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.dispatch
  repeat' first
    | (current_env_at RxHistory.activationRun; exact activationRun _)
    | publication_env_steps

theorem schedule (stack : Option Worker) : Preserves (RxHistory.schedule stack) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.schedule
  simp only [List.find?_cons,List.find?_nil]
  repeat' first
    | (current_env_at RxHistory.dispatch; exact dispatch _)
    | (current_env_at RxHistory.activationRun; exact activationRun _)
    | (current_env_at RxHistory.napiSoftirq; exact napiSoftirq)
    | (current_env_at RxHistory.audit; exact filter_probe)
    | publication_env_steps

theorem nestedResched (self : Worker) : Preserves (RxHistory.nestedResched self) := by
  unfold RxHistory.nestedResched
  apply PrefixPreserves.bind (lift_store _ (condResched_sameKernel _))
  intro b
  split
  · exact schedule _
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _

end Leanux.Proofs.WG.PublicationJoint
