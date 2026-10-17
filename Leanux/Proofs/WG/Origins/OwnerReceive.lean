import Leanux.Proofs.WG.Origins.OwnerFocus

/-! The actual UDP receive boundary transports the owner carrier using its
input allocation invariant. The private existential keeps only normal-state
allocation evidence; no claim about the outer journal follows from it. -/
namespace Leanux.Proofs.WG.OwnerReceive
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

private def Allocated (w : WGWorld) : Prop :=
  ∃ h, AllocationInv h w ∧ OwnerBounds.Carrier w

private theorem consume (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves Allocated (consumeData msg src ds) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  obtain ⟨history,allocation,carrier⟩ := hi
  have erased := (consumeDataPrefix_erases msg src ds w a history).trans hr
  have post := (consumeDataPrefix_allocation msg src ds w a history allocation).choose_spec.2.2
  change (runPrefix ((consumeDataPrefix msg src ds).run w) a history).1 =
    .ok ((result,v),b) at erased
  rw [erased] at post
  exact ⟨_,post,(hoare_iff_run_ambient _ _ _).mp
    (OwnerConsume.consumeData_spec msg src ds history) w a result v b
      ⟨allocation,carrier⟩ hr⟩

private theorem readDev : Preserves Allocated getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases hd : w.dev with
  | none => simp [getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
  | some d =>
    simp [getDev,hd] at hr
    rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩
    exact hi

private theorem modify (f : Device → Device)
    (identities : ∀ w, identityView {w with dev := w.dev.map f} = identityView w)
    (metadata : ∀ w, allocationMetadata {w with dev := w.dev.map f} = allocationMetadata w)
    (peer : ∀ d, (f d).nextPeer = d.nextPeer)
    (frontier : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs) : Preserves Allocated (modifyDev f) := by
  unfold modifyDev
  apply hoare_modify
  intro w hi
  obtain ⟨h,allocation,carrier⟩ := hi
  exact ⟨h,allocation.congr (identities w) (metadata w),
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_map)
      f peer frontier keys rx carrier⟩

private theorem queue (msg : List UInt8) (src : SkbSource) :
    Preserves Allocated (modifyDev (appendHandshakeQueue msg src)) := by
  apply modify
  · intro w
    unfold identityView Peers.snapshot keypairResidents packetResidents
    simp [appendHandshakeQueue,Option.bind_map,Function.comp_def]
  · intro w
    simp [allocationMetadata,deviceAllocationMetadata,appendHandshakeQueue,
      Option.map_map,Function.comp_def]
    rfl
  all_goals intro d; rfl

private theorem cpu (n : Int) :
    Preserves Allocated (modifyDev (setHandshakeCpu n)) := by
  apply modify
  · intro w
    unfold identityView Peers.snapshot keypairResidents packetResidents
    simp [setHandshakeCpu,Option.bind_map,Function.comp_def]
  · intro w
    simp [allocationMetadata,deviceAllocationMetadata,setHandshakeCpu,
      Option.map_map,Function.comp_def]
    rfl
  all_goals intro d; rfl

private theorem nextCpu : Preserves Allocated cpumaskNextOnline := by
  unfold cpumaskNextOnline
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head getDev; exact readDev)
    | (allocation_release_head modifyDev; exact cpu _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ Allocated)
    | allocation_release_step

private theorem packetReceive (msg : List UInt8) (src : SkbSource) :
    Preserves Allocated (WG.packetReceive msg src) := by
  unfold WG.packetReceive
  simp (config := {zeta := false}) only [branch,queueDeviceWork,unsupported,invariant]
  repeat' first
    | (allocation_release_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp Allocated)
    | (allocation_release_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp Allocated)
    | (allocation_release_head consumeData; exact consume _ _ _)
    | (allocation_release_head getDev; exact readDev)
    | (allocation_release_head modifyDev; exact queue _ _)
    | (allocation_release_head cpumaskNextOnline; exact nextCpu)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ Allocated)
    | allocation_release_step

private theorem wgReceive (msg : List UInt8) (src : SkbSource) :
    Preserves Allocated (WG.wgReceive msg src) := by
  unfold WG.wgReceive
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (allocation_release_head WG.packetReceive; exact packetReceive _ _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ Allocated)
    | allocation_release_step

theorem packetReceive_spec (msg : List UInt8) (src : SkbSource) (history : List LifetimeEvent) :
    Hoare (WG.packetReceive msg src)
      (fun w => AllocationInv history w ∧ OwnerBounds.Carrier w)
      (fun _ w => OwnerBounds.Carrier w) :=
  hoare_consequence (packetReceive msg src) (fun _ hi => ⟨history,hi⟩)
    (fun _ _ hi => hi.choose_spec.2)

theorem wgReceive_spec (msg : List UInt8) (src : SkbSource) (history : List LifetimeEvent) :
    Hoare (WG.wgReceive msg src)
      (fun w => AllocationInv history w ∧ OwnerBounds.Carrier w)
      (fun _ w => OwnerBounds.Carrier w) :=
  hoare_consequence (wgReceive msg src) (fun _ hi => ⟨history,hi⟩)
    (fun _ _ hi => hi.choose_spec.2)

theorem packetReceive_checked (msg : List UInt8) (src : SkbSource) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (packetReceivePrefix msg src))) :=
  OwnerChecks.native_mixed _ _ (packetReceivePrefix_erases msg src)
    (packetReceivePrefix_preserves allocationAmbient allocationReceiveIngress msg src)
    (Origins.Retaining.packetReceive_material msg src)
    (CurrentRx.packetReceive_preserves msg src)
    (packetReceive_spec msg src)

theorem wgReceive_checked (msg : List UInt8) (src : SkbSource) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  OwnerChecks.native_mixed _ _ (wgReceivePrefix_erases msg src)
    (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress msg src)
    (Origins.Retaining.wgReceive_material msg src)
    (CurrentRx.wgReceive_preserves msg src)
    (wgReceive_spec msg src)

end Leanux.Proofs.WG.OwnerReceive
