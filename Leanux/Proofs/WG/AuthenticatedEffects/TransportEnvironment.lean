import Leanux.Proofs.WG.AuthenticatedEffects.TransportWorkers
import Leanux.Proofs.WG.Packets.PublicationEnvironment

/-! Original scheduler composition of pre-consume authentication receipts.
Native state preservation is reused from campaign 1; only the real receive
polls can introduce this layer's additional checked-counter certificates. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportChecks
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Origins CurrentEnvironment

private theorem mixed_lift (a : Leanux.M α) (frame : SameProductStore a) :
    Preserves (RxHistory.mixed (liftPrefix a)) := mixed _
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.mixed_lift) a frame)
private theorem mixed_throw (e : Stop) : Preserves (RxHistory.mixed (throw e : PrefixM LifetimeEvent α)) := mixed _
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.mixed_throw) e)
private theorem peer (pid : PeerId) : Preserves (RxHistory.mixed (liftWGObserver (getPeerMixed pid))) := mixed _
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.peer) pid)
private theorem packet (id : SkbId) : Preserves (RxHistory.mixed (liftWGObserver (getTxSkbPrefix id))) := mixed _
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.packet) id)
private theorem work (f : List PeerId → List PeerId) :
    Preserves (RxHistory.mixed (liftWGObserver
      (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})))) := mixed _
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.work) f)
private theorem occupancy (a : Activation) : Preserves (RxHistory.mixed (activationOccupancyPrefix a)) := mixed _
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.occupancy) a)
private theorem hasWork (a : Activation) : Preserves (RxHistory.mixed (activationHasWorkPrefix a)) := mixed _
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.hasWork) a)
private theorem pendingNapi (next : Option Nat) : Preserves (RxHistory.mixed (pendingNapiPrefix next)) := mixed _
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.pendingNapi) next)

theorem filter_probe : Preserves (RxHistory.audit consistentFilterAudit) :=
  audit _ PublicationJoint.filter_probe

theorem receiveStep : Preserves HistoryAdapters.receiveStep :=
  quiet _ PublicationJoint.receiveStep (HistoryAdapters.focus_other sensitive
    (by intro event; cases event <;> rfl) _)

theorem receiveIteration : Preserves HistoryAdapters.receiveIteration := by
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) receiveStep
  exact lift_store _ (condResched_sameKernel .receiveWorker)

theorem txIteration (pid : PeerId) :
    Preserves (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  mixed _ (PublicationJoint.txIteration pid)

theorem encryptIteration : Preserves RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  exact (mixed _ (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEncrypt.«0».Leanux.Proofs.WG.PublicationJoint.encryptPoll)).bind
    (fun item => napiSoftirq.bind (fun _ => mixed _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEncrypt.«0».Leanux.Proofs.WG.PublicationJoint.encryptTail) item)))

macro "transport_env_steps" : tactic => `(tactic| first
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
  | (current_env_at Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (current_env_at ForIn.forIn; first
      | apply PrefixPreserves.range (State := World) _ _ _ (fun _ _ hi => hi.2)
      | apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.2))
  | (current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (current_env_at ite; split)
  | current_env_match
  | support_intro)

theorem cryptAhead (pid : PeerId) : Preserves (RxHistory.cryptAhead pid) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.cryptAhead
  repeat' first
    | (current_env_at RxHistory.encryptIteration; exact encryptIteration)
    | transport_env_steps

theorem activationIteration (a : Activation) : Preserves (RxHistory.activationIteration a) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.activationIteration
  repeat' first
    | (current_env_at RxHistory.encryptIteration; exact encryptIteration)
    | (current_env_at RxHistory.decryptIteration; exact decryptIteration)
    | (current_env_at RxHistory.cryptAhead; exact cryptAhead _)
    | transport_env_steps

theorem activationRun (a : Activation) : Preserves (RxHistory.activationRun a) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.activationRun
  repeat' first
    | (current_env_at RxHistory.activationIteration; exact activationIteration _)
    | transport_env_steps

theorem dispatch (worker : Worker) : Preserves (RxHistory.dispatch worker) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.dispatch
  repeat' first
    | (current_env_at RxHistory.activationRun; exact activationRun _)
    | transport_env_steps

theorem schedule (stack : Option Worker) : Preserves (RxHistory.schedule stack) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.schedule
  simp only [List.find?_cons,List.find?_nil]
  repeat' first
    | (current_env_at RxHistory.dispatch; exact dispatch _)
    | (current_env_at RxHistory.activationRun; exact activationRun _)
    | (current_env_at RxHistory.napiSoftirq; exact napiSoftirq)
    | (current_env_at RxHistory.audit; exact filter_probe)
    | transport_env_steps

theorem nestedResched (self : Worker) : Preserves (RxHistory.nestedResched self) := by
  unfold RxHistory.nestedResched
  apply PrefixPreserves.bind (lift_store _ (condResched_sameKernel _))
  intro b
  split
  · exact schedule _
  · exact PrefixPreserves.pure (fun _ _ hi => hi.2) _

end Leanux.Proofs.WG.AuthenticatedEffects.TransportChecks
