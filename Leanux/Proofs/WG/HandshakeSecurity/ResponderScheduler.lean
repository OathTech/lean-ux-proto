import Leanux.Proofs.WG.HandshakeSecurity.ResponderTransmitFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Joint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins CurrentEnvironment

theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) : Preserves (liftPrefix a) :=
  from_global _ (PublicationJoint.lift_store a frame) (Global.lift_store a frame)

theorem mixed_lift (a : Leanux.M α) (frame : SameProductStore a) : Preserves (RxHistory.mixed (liftPrefix a)) :=
  from_global _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.mixed_lift) a frame)
    (Global.mixed _ _ (erasesPrefix_lift _) (native_product_store frame))

theorem mixed_throw (e : Stop) : Preserves (RxHistory.mixed (throw e : PrefixM LifetimeEvent α)) :=
  from_global _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.mixed_throw) e)
    (Global.mixed _ _ (erasesPrefix_throw e) (native_product_store (HistorySupport.source_throw _ e)))

theorem peer (pid : PeerId) : Preserves (RxHistory.mixed (liftWGObserver (getPeerMixed pid))) :=
  from_global _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.peer) pid)
    (Global.native_mixed _ _ (getPeerMixed_erases pid) (readPeer_native pid))

theorem packet (id : SkbId) : Preserves (RxHistory.mixed (liftWGObserver (getTxSkbPrefix id))) :=
  from_global _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.packet) id)
    (Global.native_mixed _ _ (getTxSkbPrefix_erases id) (fun confirmed => by unfold getTxSkb; exact native_skb _ confirmed))

theorem work (f : List PeerId → List PeerId) : Preserves (RxHistory.mixed (liftWGObserver
    (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})))) :=
  from_global _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.work) f)
    (Global.native_mixed _ _ (erasesStatePrefix_lift _) (modify_native _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)))

theorem occupancy (a : Activation) : Preserves (RxHistory.mixed (activationOccupancyPrefix a)) :=
  from_global _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.occupancy) a)
    (Global.mixed _ _ (activationOccupancyPrefix_erases a) (native_product_store (activationOccupancy_sameKernel a)))

theorem hasWork (a : Activation) : Preserves (RxHistory.mixed (activationHasWorkPrefix a)) :=
  from_global _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.hasWork) a)
    (Global.mixed _ _ (activationHasWorkPrefix_erases a) (native_product_store (activationHasWork_sameKernel a)))

theorem pendingNapi (next : Option Nat) : Preserves (RxHistory.mixed (pendingNapiPrefix next)) := by
  apply from_global _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.pendingNapi) next)
  apply Global.mixed _ _ (pendingNapiPrefix_erases next)
  intro confirmed
  apply native_product_store
  unfold Lifetimes.pendingNapi
  exact SameView.bind (liftWG_sameProductStore getDev getDev_sameWGStore) (fun _ => SameView.pure _ _)

theorem refills : Preserves (RxHistory.mixed activationRefillsPrefix) :=
  from_global _ (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationEnvironment.«0».Leanux.Proofs.WG.PublicationJoint.refills)
    (Global.mixed _ _ activationRefillsPrefix_erases (native_product_store activationRefills_sameKernel))

theorem filter_probe : Preserves (RxHistory.audit consistentFilterAudit) := by
  apply from_global _ PublicationJoint.filter_probe
  apply Global.audited _ _ consistentFilterAudit_erases
  intro confirmed
  apply native_product_store
  apply SameView.bind
  · intro initial
    exact productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi)
  · intro ambient
    exact filterM_sameKernel productStoreView _ activationConsistent_sameKernel _

theorem napiSoftirq (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Preserves RxHistory.napiSoftirq :=
  from_global _ PublicationJoint.napiSoftirq (Global.napiSoftirq H1 slots)

theorem encryptIteration (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Preserves RxHistory.encryptIteration :=
  from_global _ PublicationJoint.encryptIteration (Global.encryptIteration H1 slots)

theorem decryptIteration (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Preserves RxHistory.decryptIteration :=
  from_global _ PublicationJoint.decryptIteration (Global.decryptIteration H1 slots)

macro "responder_env_steps " H1:term : tactic => `(tactic| first
  | (current_env_at HistoryAdapters.receiveIteration; exact receiveIteration $H1)
  | (current_env_at getPeerMixed; exact peer _)
  | (current_env_at getTxSkbPrefix; exact packet _)
  | (current_env_at activationOccupancyPrefix; exact occupancy _)
  | (current_env_at activationRefillsPrefix; exact refills)
  | (current_env_at Env.pendingDevice; exact lift_store _ (pendingDevice_sameKernel _ _))
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
     simp only [getAmbient, hidden, peekHiddenSite, recordBudget, budgetExhausted, peekUnit, resolveUnit, modifyAmbient, invariant, unsupported]
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

theorem cryptAhead (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (pid : PeerId) : Preserves (RxHistory.cryptAhead pid) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.cryptAhead
  repeat' first
    | (current_env_at RxHistory.encryptIteration; exact encryptIteration H1 slots)
    | responder_env_steps H1

theorem activationIteration (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (a : Activation) : Preserves (RxHistory.activationIteration a) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.activationIteration
  repeat' first
    | (current_env_at RxHistory.encryptIteration; exact encryptIteration H1 slots)
    | (current_env_at RxHistory.decryptIteration; exact decryptIteration H1 slots)
    | (current_env_at RxHistory.cryptAhead; exact cryptAhead H1 slots _)
    | responder_env_steps H1

theorem activationRun (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (a : Activation) : Preserves (RxHistory.activationRun a) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.activationRun
  repeat' first
    | (current_env_at RxHistory.activationIteration; exact activationIteration H1 slots _)
    | responder_env_steps H1

theorem dispatch (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (worker : Worker) : Preserves (RxHistory.dispatch worker) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.dispatch
  repeat' first
    | (current_env_at RxHistory.activationRun; exact activationRun H1 slots _)
    | responder_env_steps H1

theorem schedule (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (stack : Option Worker) : Preserves (RxHistory.schedule stack) := by
  change PrefixPreserves Inv Safe _
  unfold RxHistory.schedule
  simp only [List.find?_cons, List.find?_nil]
  repeat' first
    | (current_env_at RxHistory.dispatch; exact dispatch H1 slots _)
    | (current_env_at RxHistory.activationRun; exact activationRun H1 slots _)
    | (current_env_at RxHistory.napiSoftirq; exact napiSoftirq H1 slots)
    | (current_env_at RxHistory.audit; exact filter_probe)
    | responder_env_steps H1

theorem nestedResched (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (self : Worker) : Preserves (RxHistory.nestedResched self) := by
  unfold RxHistory.nestedResched
  apply PrefixPreserves.bind (lift_store _ (condResched_sameKernel _))
  intro b
  split
  · exact schedule H1 slots _
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Joint
