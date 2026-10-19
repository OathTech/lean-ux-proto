import Leanux.Proofs.WG.Config.ScalarTailFrames
import Leanux.Proofs.WG.Config.ScalarFinishSource
import Leanux.Proofs.WG.Config.ScalarPrefixSource
import Leanux.Proofs.WG.Index.ConfigurationPeerSource

/-! Whole acquired-update scalar effects for arbitrary later attributes, including actual allowed-IP errors, replacement, staging and final payment. Funding and base-list membership recover the final selected incarnation from the same run. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarTail
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention ScalarFinish

theorem tail_selected (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (expected : Cell) :
    Hoare (Configuration.peerConfigTailSource attrs peer pid)
      (fun g=>Selected pid expected (view g))
      (fun result g=>Selected pid (tailCell attrs result expected) (view g)) := by
  rw [Configuration.peerConfigTailSource_factor]
  apply Index.ConfigurationIndex.allowedIps_results_rule
    (fun g=>Selected pid expected (view g))
    (fun result g=>Selected pid (tailCell attrs result expected) (view g))
    attrs peer pid _
  · intro ip _
    exact (ScalarAllowed.allowed_frame pid ip).wp (Selected pid expected)
  · intro ret negative
    exact hoare_consequence (out_selected attrs peer pid ret expected)
      (fun _ h=>h) (fun result g post=>by
        obtain ⟨rfl,post⟩:=post
        simpa only [tailCell,negative,ite_true] using post)
  · intro ret nonnegative
    exact hoare_consequence (finish_selected attrs peer pid ret expected)
      (fun _ h=>h) (fun result g post=>by
        obtain ⟨rfl,post⟩:=post
        simpa only [tailCell,show ¬result<0 by omega,ite_false] using post)

theorem tail_exact (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (expected : Cell) :
    Noise.Ensures (Configuration.peerConfigTailSource attrs (some paid.slot) paid.slot)
      (fun g=>Index.ConfigurationIndex.Entry cs (paid::loans) g ∧
        paid.slot∈BaseCoherence.slots g ∧ view g paid.slot=some expected)
      (fun result g=>Index.ConfigurationIndex.Entry cs loans g ∧
        view g paid.slot=some (tailCell attrs result expected)) := by
  intro g a result final b pre run
  have account := (hoare_iff_run_ambient _ _ _).mp
    (Index.ConfigurationIndex.tail_entry cs loans paid attrs) g a result final b pre.1 run
  have same := congrArg Prod.fst ((ProjectedAction.iff_run_ambient _ _ _).mp
    (BaseCoherence.tail_view attrs (some paid.slot) paid.slot) g a result final b run)
  change BaseCoherence.slots final=BaseCoherence.slots g at same
  have member : paid.slot∈BaseCoherence.slots final := by rw [same]; exact pre.2.1
  obtain ⟨d,p,device,resident⟩ := base_resident cs loans paid.slot final account member
  have found : view final paid.slot=some (cell p) := by
    simp only [view,peerValues,device,Option.bind_some,resident,Option.map_some]
  have scalar := (hoare_iff_run_ambient _ _ _).mp
    (tail_selected attrs (some paid.slot) paid.slot expected) g a result final b
    (selected_initial paid.slot expected (view g) pre.2.2) run
  exact ⟨account,by rw [found,scalar (cell p) found]⟩

theorem updatePrefix_factor (attrs : PeerAttrs) (paid : Owner) (flags : UInt32) (psk : Option Key) :
    HolderConfigUpdate.updatePrefix attrs paid flags psk = (do
      ScalarPrefix.scalarPrefix attrs psk paid.slot
      if ←branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS !=0) then
        removeByPeer paid.slot) := by
  cases endpoint : attrs.endpoint <;>
    simp only [HolderConfigUpdate.updatePrefix,ScalarPrefix.scalarPrefix,
      ScalarPrefix.pskSource,ScalarPrefix.endpointSource,endpointAttributeUpdate,endpoint,
      bind_assoc,pure_bind,Queues.RxCredits.bind_if_source]

theorem updatePrefix_fields (attrs : PeerAttrs) (paid : Owner) (flags : UInt32)
    (psk : Option Key) (d : Device) (p : Peer) (resident : d.peers[paid.slot]?=some p) :
    Noise.Ensures (HolderConfigUpdate.updatePrefix attrs paid flags psk)
      (fun g=>g.dev=some d)
      (fun _ g=>view g paid.slot=some (prefixCell p psk attrs.endpoint) ∧
        BaseCoherence.slots g=d.peerList) := by
  intro g a result final b device run
  rw [updatePrefix_factor] at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,middle,c,scalar,replace⟩:=run
  have effect := ScalarPrefix.prefix_exact attrs psk paid.slot d p resident g.nlSock7
    g.fixtureNetDevices g a ignored middle c ⟨device,rfl,rfl⟩ scalar
  obtain ⟨reset,changed,_⟩:=effect
  have fields:=ScalarPrefix.effect_fields d paid.slot p psk attrs.endpoint reset resident
  have saved:= (ProjectedAction.iff_run_ambient _ _ _).mp
    (replacement_frame paid.slot flags) middle c result final b replace
  have scalarMap := congrArg Prod.fst saved
  change view final=view middle at scalarMap
  have slots := congrArg (fun s=>s.2.1) saved
  change BaseCoherence.slots final=BaseCoherence.slots middle at slots
  constructor
  · rw [scalarMap]
    simp only [view,peerValues,changed,Option.bind_some,fields.1,Option.map_some,prefixCell_reset]
  · rw [slots]
    have lists:=congrArg Device.peerList fields.2.1
    simpa only [BaseCoherence.slots,changed,Option.map_some,Option.getD_some,withoutPeers] using lists

theorem update_exact (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (keep : flags &&& WGPEER_F_REMOVE_ME=0)
    (d : Device) (p : Peer) (resident : d.peers[paid.slot]?=some p)
    (member : paid.slot∈d.peerList) :
    Noise.Ensures (Configuration.peerConfigUpdateSource attrs (some paid.slot) flags psk paid.slot)
      (fun g=>Index.ConfigurationIndex.Entry cs (paid::loans) g ∧ g.dev=some d)
      (fun result g=>Index.ConfigurationIndex.Entry cs loans g ∧
        view g paid.slot=some (tailCell attrs result (prefixCell p psk attrs.endpoint))) := by
  intro g a result final b pre run
  rw [HolderConfigUpdate.update_factor] at run
  have no : (flags &&& WGPEER_F_REMOVE_ME !=0)=false := by simp [keep]
  simp only [no] at run
  change ((HolderConfigUpdate.updateTail attrs paid flags psk).run g).run
    (CounterWindow.record a .peerRemoveMe false)=.ok ((result,final),b) at run
  rw [HolderConfigUpdate.tail_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,middle,c,prefixRun,tailRun⟩:=run
  have fields:=updatePrefix_fields attrs paid flags psk d p resident g _ ignored middle c pre.2 prefixRun
  have account:=(hoare_iff_run_ambient _ _ _).mp
    (Index.ConfigurationIndex.updatePrefix_entry cs (paid::loans) attrs paid flags psk)
    g _ ignored middle c pre.1 prefixRun
  exact tail_exact cs loans paid attrs (prefixCell p psk attrs.endpoint) middle c result final b
    ⟨account,by rw[fields.2];exact member,fields.1⟩ tailRun

end Leanux.Proofs.WG.Config.ScalarTail
