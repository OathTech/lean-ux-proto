import Leanux.Proofs.WG.Config.ConfiguredBoundaryBridge
import Leanux.Proofs.WG.Config.ConfiguredRemovalSource
import Leanux.Proofs.WG.Index.ConfigurationPeersSource
import Leanux.Proofs.WG.AllowedIps.RoutingAcquire
import Leanux.Proofs.WG.Configuration.PeerTailCompletion

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

/-- Representation retention and unchanged base list share one concrete cut. -/
theorem retained_ready {α : Type} (action : WG.M α)
    (routing : RetainsRoutingCall action)
    (base : SameView BaseCoherence.view action) :
    Preserves Ready action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  obtain ⟨d,device,t4,t6,represented,owners⟩ := pre
  have retained := (ProjectedAction.iff_run_ambient _ _ _).mp routing g a result v b run
  have listed := congrArg Prod.fst
    ((ProjectedAction.iff_run_ambient _ _ _).mp base g a result v b run)
  change BaseCoherence.slots v=BaseCoherence.slots g at listed
  change RetainsRouting (routingView g) (routingView v) at retained
  cases final : v.dev with
  | none => simp [routingView,device,final,RetainsRouting] at retained
  | some out =>
    have effect : (routingState d).Retains (routingState out) := by
      simpa only [routingView,device,final,Option.map_some,RetainsRouting] using retained
    have same : out.peerList=d.peerList := by
      simpa only [BaseCoherence.slots,device,final,Option.map_some,Option.getD_some] using listed
    exact ⟨out,final,t4,t6,represented.of_retains effect,
      configured_of_list d out t4 t6 owners (fun _ member=>same.symm ▸ member)⟩

theorem create_ready (key : Key) (psk : Option Key) :
    Ensures (peerCreate key psk) Ready (fun result g =>
      Ready g ∧ ∀ pid, result=.ok pid → pid ∈ BaseCoherence.slots g) := by
  intro g a result v b pre run
  obtain ⟨d,device,t4,t6,represented,owners⟩ := pre
  obtain ⟨out,final,next⟩ := peerCreate_routing_preserved g v a b d device represented key psk result run
  have list := BaseCoherence.creation_view key psk g v a b run
  cases result with
  | error code =>
    have same : out.peerList=d.peerList := by
      simpa only [BaseCoherence.view,BaseCoherence.slots,device,final,
        Option.map_some,Option.getD_some] using congrArg Prod.fst list
    exact ⟨⟨out,final,t4,t6,next,
      configured_of_list d out t4 t6 owners (fun _ member=>same.symm ▸ member)⟩,
      fun _ equal=>by cases equal⟩
  | ok pid =>
    obtain ⟨old,oldDevice,_,published⟩ := list
    have equal : old=d := Option.some.inj (oldDevice.symm.trans device)
    subst old
    have same : out.peerList=d.peerList++[pid] := by
      have fields := Option.some.inj (by simpa only [final,Option.map_some] using published)
      exact congrArg Prod.fst fields
    refine ⟨⟨out,final,t4,t6,next,
      configured_of_list d out t4 t6 owners (fun _ member=>same.symm ▸ List.mem_append_left _ member)⟩,?_⟩
    intro selected equal
    cases equal
    simp [BaseCoherence.slots,final,same]

theorem removeByPeer_ready (pid : PeerId) : Preserves Ready (removeByPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  cases result
  obtain ⟨d,device,t4,t6,represented,owners⟩ := pre
  obtain ⟨p,resident⟩ := removeByPeer_input_resident g v a b d pid device run
  obtain ⟨out,reached,inputs,actual,state,_,next⟩ :=
    removeByPeer_routing_total g a d device pid p resident t4 t6 represented
  cases actual.symm.trans run
  have final : v.dev=some out := by rw [state]
  have base := congrArg Prod.fst
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.removeByPeer_view pid)
      g a () v b run)
  change BaseCoherence.slots v=BaseCoherence.slots g at base
  have same : out.peerList=d.peerList := by
    simpa only [BaseCoherence.slots,device,final,Option.map_some,Option.getD_some] using base
  refine ⟨out,final,_,_,next,?_⟩
  intro e member
  rw [Tree.eraseIds_entries,Tree.eraseIds_entries,←List.filter_append] at member
  exact same.symm ▸ owners e (List.mem_filter.mp member).1

theorem removeByPeer_selected (pid : PeerId) :
    Preserves (Selected pid) (removeByPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  have same := congrArg Prod.fst
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.removeByPeer_view pid)
      g a result v b run)
  change BaseCoherence.slots v=BaseCoherence.slots g at same
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (removeByPeer_ready pid)
    g a result v b pre.1 run,same.symm ▸ pre.2⟩

theorem finish_ready (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Preserves Ready (peerTailFinishSource attrs peer pid ret) :=
  retained_ready _ (peerTailFinishSource_routing attrs peer pid ret)
    (BaseCoherence.tailFinish_view attrs peer pid ret)

theorem staged_ready (pid : PeerId) : Preserves Ready (sendStagedPackets pid) :=
  retained_ready _ (sendStagedPackets_routing pid) (BaseCoherence.staged_view pid)

theorem keepalive_ready (pid : PeerId) : Preserves Ready (sendKeepalive pid) :=
  retained_ready _ (sendKeepalive_routing pid) (BaseCoherence.keepalive_view pid)

theorem create_entry (cs : Ledger) (loans : Reservations) (key : Key) (psk : Option Key) :
    Ensures (peerCreate key psk) (Entry cs loans) (fun result g =>
      Entry cs loans g ∧ ∀ pid, result=.ok pid → pid ∈ BaseCoherence.slots g) := by
  intro g a result v b pre run
  have out := create_ready key psk g a result v b pre.2 run
  exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp
    (Index.ConfigurationIndex.creation_entry cs loans key psk) g a result v b pre.1 run,
    out.1⟩,out.2⟩

theorem removeByPeer_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (removeByPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
    (Index.ConfigurationIndex.removeByPeer_entry cs loans pid) g a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp (removeByPeer_ready pid) g a result v b pre.2 run⟩

theorem finish_entry (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (ret : Int) :
    Hoare (peerTailFinishSource attrs (some paid.slot) paid.slot ret)
      (Entry cs (paid::loans)) (fun _=>Entry cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
    (Index.ConfigurationIndex.finish_entry cs loans paid attrs ret) g a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp (finish_ready attrs (some paid.slot) paid.slot ret)
      g a result v b pre.2 run⟩

theorem paid_resident (cs : Ledger) (loans : Reservations) (paid : Owner)
    (g : WGWorld) (d : Device) (device : g.dev=some d)
    (entry : Index.ConfigurationIndex.Entry cs (paid::loans) g) :
    ∃ p,d.peers[paid.slot]?=some p := by
  obtain ⟨holders,funded,_⟩ := entry.1.1
  have charged : 0 < demand cs (holders.owners ++ (paid::loans)) paid := by
    simp only [demand,List.count_append,List.count_cons_self]
    omega
  obtain ⟨p,found,_⟩ := protected_resident funded.carriers.funded charged
  obtain ⟨old,present,_,resident,_⟩ := resident_fields found
  have same : old=d := Option.some.inj (present.symm.trans device)
  subst old
  exact ⟨p,resident⟩

theorem allowed_entry (cs : Ledger) (loans : Reservations) (paid : Owner)
    (ip : AllowedIpAttrs) (shape : AddressShape ip) :
    Preserves (SelectedEntry cs (paid::loans) paid.slot) (setAllowedip paid.slot ip) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a ret v b pre run
  obtain ⟨d,device,t4,t6,routing,owners⟩ := pre.1.2
  obtain ⟨p,resident⟩ := paid_resident cs loans paid g d device pre.1.1
  have member : paid.slot∈d.peerList := by
    simpa only [BaseCoherence.slots,device,Option.map_some,Option.getD_some] using pre.2
  obtain ⟨out,present,effect⟩ := setAllowedip_routingEffect d t4 t6 paid.slot p ip
    shape routing resident g a ret v b device run
  obtain ⟨u4,u6,next,configured⟩ :=
    allowedipRoutingEffect_configured d out t4 t6 paid.slot ip ret routing owners member effect
  have base := congrArg Prod.fst
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.setAllowedip_view paid.slot ip)
      g a ret v b run)
  change BaseCoherence.slots v=BaseCoherence.slots g at base
  exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp
    (Index.ConfigurationIndex.setAllowedip_entry cs (paid::loans) paid.slot ip)
      g a ret v b pre.1.1 run,⟨out,present,u4,u6,next,configured⟩⟩,base.symm ▸ pre.2⟩

theorem out_ready (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Preserves Ready (do
      peerPut peer
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int) :=
  preserves_bind (retained_ready _ (peerPut_retainsRouting peer) (BaseCoherence.peerPut_view peer))
    (fun _=>preserves_bind
      (hoare_liftAmbient (AmbientM.branch .peerZeroPsk attrs.presharedKey.isSome) Ready)
      (fun _=>preserves_pure ret))

theorem out_entry (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (ret : Int) :
    Hoare (do peerPut (some paid.slot)
              _ ← branch .peerZeroPsk attrs.presharedKey.isSome
              pure ret : WG.M Int)
      (Entry cs (paid::loans)) (fun _=>Entry cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
    (Index.ConfigurationIndex.out_entry cs loans paid attrs ret) g a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp (out_ready attrs (some paid.slot) ret)
      g a result v b pre.2 run⟩

/-- Every original tail return pays its selected caller occurrence, including
malformed entries and negative insertion results. Only actual list members
need the address shape supplied by the enclosing parsed configuration. -/
theorem tail_entry (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (shape : PeerAddressShape attrs) :
    Hoare (Configuration.peerConfigTailSource attrs (some paid.slot) paid.slot)
      (SelectedEntry cs (paid::loans) paid.slot) (fun _=>Entry cs loans) := by
  rw [peerConfigTailSource_factor]
  apply Index.ConfigurationIndex.allowedIps_members_rule
  · intro ip member
    exact allowed_entry cs loans paid ip (shape ip member)
  · intro ret
    exact hoare_consequence (out_entry cs loans paid attrs ret) (fun _ pre=>pre.1) (fun _ _ pre=>pre)
  · intro ret
    exact hoare_consequence (finish_entry cs loans paid attrs ret) (fun _ pre=>pre.1) (fun _ _ pre=>pre)

end Leanux.Proofs.WG.Config.OwnerConfiguration
