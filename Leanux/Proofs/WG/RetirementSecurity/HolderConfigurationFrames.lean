import Leanux.Proofs.WG.RetirementSecurity.HolderKeepalive
import Leanux.Proofs.WG.RetirementSecurity.RemovalOwnershipFrames
import Leanux.Proofs.WG.Queues.HolderConfigUpdate
import Leanux.Proofs.WG.Queues.SlotConfiguration

/-! Native routing/configuration edits retain exact key demand and the actual
acquired caller's spare peer reference. Routing-node allocation is independent
of key credit; its original lifetime observer transports allocation bounds. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits StackOwnership HolderConsume HolderKeepalive
variable {selected : PeerId}

def fields (w : WGWorld) := (ownershipPointView w,peerView w)

theorem fields_update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId)
    (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue)
    (owns : ∀p,peerOwnership (f p)=peerOwnership p) :
    SameView fields (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact Prod.ext ((ProjectedAction.iff_run_ambient _ _ _).mp
    (show SameView ownershipPointView (getPeer pid >>= fun p => setPeer pid (f p)) from by
      intro initial
      apply hoare_bind _ _ (ownership_getPeer (·=initial) pid)
      intro p
      apply hoare_consequence (ownership_setPeer (·=initial) pid (f p))
      · intro z h
        exact ⟨h.1,by simpa only [owns] using h.2⟩
      · intro _ _ h; exact h) w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (peers_update pid f stamp count rx) w a result v b run)

theorem store_fields {action : WG.M α} (same : SameWGStore action) : SameView fields action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact Prod.ext ((ProjectedAction.iff_run_ambient _ _ _).mp (ownershipPoints_kernel _ same) w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (peers_store same) w a result v b run)

private theorem aip_fields (action : AipM α) : SameView fields (liftAip action) := by
  intro initial
  apply hoare_liftAip
  intro w d table before device
  unfold fields ownershipPointView RetirementSecurity.keyReferenceView RetirementSecurity.keyAt
    ownershipAt peerAt packetKeyWords peerView at before ⊢
  simpa only [device,Option.bind_some,Option.map_some,Option.isSome_some] using before

private def clearFields (s : WGStoreView × (PeerId → Option Peer)) :=
  let w : WGWorld := {dev:=s.1.dev}
  ((RetirementSecurity.keyReferenceView w,
    s.1.dev.isSome,(fun pid => (s.2 pid).map peerOwnership),
    (packetKeyWords w).1,(packetKeyWords w).2),
   (s.1.dev.map Device.ifindex,fun pid => (s.2 pid).map fun p => (p.internalId,p.refcount,p.rxQueue)))

private theorem clear_factor (w : WGWorld) : clearFields (AllowedIps.clearListView w)=fields w := by
  unfold clearFields AllowedIps.clearListView fields ownershipPointView RetirementSecurity.keyReferenceView
    RetirementSecurity.keyAt ownershipAt peerAt packetKeyWords peerView
  simp only [Option.bind_map,Option.map_bind,Option.map_map,Function.comp_def,Option.isSome_map]
  rfl

theorem list_delete (id : NodeId) : SameView fields (listDel id) :=
  (AllowedIps.listDel_clearListView id).of_factor clearFields fields (fun w => (clear_factor w).symm)

theorem list_add (pid : PeerId) (id : NodeId) : SameView fields (listAddTail pid id) := by
  exact fields_update pid (fun p => {p with allowedipsList:=p.allowedipsList++[id]})
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)

macro "configuration_fields_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact (aip_fields _).wp (·=$initial))
  | (rx_retention_head liftAip; exact (aip_fields _).wp (·=$initial))
  | (rx_retention_head getDev; exact (store_fields getDev_sameWGStore).wp (·=$initial))
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

theorem add_fields (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView fields (add root bits key cidr peer) := by
  intro initial
  change Preserves (fun w => fields w=initial) _
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listDel; exact (list_delete _).wp (·=initial))
    | (rx_retention_head listAddTail; exact (list_add _ _).wp (·=initial))
    | configuration_fields_step initial

theorem insert_fields (family addr cidr : Nat) (pid : PeerId) :
    SameView fields (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w => fields w=initial) _
  unfold WG.insert
  apply preserves_bind ?_
  · intro _
    split <;> exact (add_fields _ _ _ _ _).wp (·=initial)
  · apply hoare_modify
    intro w before
    unfold fields ownershipPointView RetirementSecurity.keyReferenceView RetirementSecurity.keyAt
      ownershipAt peerAt packetKeyWords peerView at before ⊢
    cases device : w.dev <;> simpa [device] using before

theorem allowedip_fields (pid : PeerId) (ip : AllowedIpAttrs) : SameView fields (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w => fields w=initial) _
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact (insert_fields _ _ _ _).wp (·=initial))
    | configuration_fields_step initial

theorem join {observer : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix observer native)
    (allocation : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe observer)
    (same : SameView fields native) (slots : Preserves CurrentSlots.Inv native) :
    Preserves (HolderKeepalive.Selected temporary selected) native := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have view := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  exact ⟨⟨before.1.1.points (congrArg Prod.fst view),
    Allocated.native erases allocation before.1.2.1 a b run,
    (hoare_iff_run_ambient _ _ _).mp slots w a result v b before.1.2.2 run⟩,
    before.2.view (congrArg Prod.snd view)⟩

theorem allowedip (pid : PeerId) (ip : AllowedIpAttrs) :
    Preserves (HolderKeepalive.Selected temporary selected) (setAllowedip pid ip) :=
  join (ConfigurationCall.erases (.allowedIp pid ip)) (ConfigurationCall.allocation (.allowedIp pid ip))
    (allowedip_fields pid ip) (CurrentSlots.Configuration.allowedip pid ip)

theorem store {action : WG.M α} (same : SameWGStore action) :
    Preserves (HolderKeepalive.Selected temporary selected) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have shape := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  have view := (ProjectedAction.iff_run_ambient _ _ _).mp (store_fields same) w a result v b run
  exact ⟨⟨before.1.1.points (congrArg Prod.fst view),before.1.2.1.store shape,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.view_preserves (project:=id)
      (Affiliation.kernel same)) w a result v b before.1.2.2 run⟩,
    before.2.view (congrArg Prod.snd view)⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderConfiguration
