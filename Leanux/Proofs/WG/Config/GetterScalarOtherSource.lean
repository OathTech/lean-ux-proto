import Leanux.Proofs.WG.Config.GetterScalarOtherFrames
import Leanux.Proofs.WG.Config.CommandScalarRulesSource
import Leanux.Proofs.WG.Config.CreationCommandSource
import Leanux.Proofs.WG.Config.KeyScalarFrames
import Leanux.Proofs.WG.Config.UpdateOnlySource

/-! Actual command selection, creation and update source composition. All accounting premises refer to the same execution. Invalid requests and REMOVE_ME have global deletion-aware retention; accepted edits retain every surviving nonselected incarnation. Original Stops are retained; only normal endpoints are claimed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar.Other
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do Queues
open Queues.RxCredits Leanux.Proofs.WG.Configuration

theorem endpoint (selected : PeerId) (entry : GetterScalar.Map) (e : Endpoint) :
    Preserves (Holds selected entry) (setPeerEndpoint selected e) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  by_cases valid:e.family=AF_INET ∨ e.family=AF_INET6
  · have cut:=run
    unfold setPeerEndpoint at cut
    simp only [requireNotPending,pure_bind] at cut
    rw [MaterialOrigin.bind_ok_ambient] at cut
    obtain ⟨p,u,c,read,_⟩:=cut
    obtain ⟨_,_,d,device,resident⟩:=getPeer_normal selected g u p a c read
    obtain ⟨reset,effect,_,_⟩:=setPeerEndpoint_exact selected e d p resident valid
      g.nlSock7 g.fixtureNetDevices g a result final b ⟨device,rfl,rfl⟩ run
    intro pid value other present
    apply pre pid value other
    simp only [GetterScalar.view,GetterScalar.values,effect,Option.bind_some] at present
    simp only [GetterScalar.view,GetterScalar.values,device,Option.bind_some]
    unfold endpointStores at present
    split at present
    · exact present
    · cases reset <;>
        simpa [withPeer,Std.TreeMap.getElem?_insert,Ne.symm other] using present
  · have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (Roaming.RemoteControl.setPeerEndpoint_invalid selected e
        (fun h=>valid (Or.inl h)) (fun h=>valid (Or.inr h))) g a result final b run
    exact same ▸ pre

theorem staged (selected : PeerId) (entry : GetterScalar.Map) :
    Preserves (Holds selected entry) (sendStagedPackets selected) :=
  retained selected entry _ (fun initial=>GetterScalar.staged initial selected)

theorem keepalive (selected : PeerId) (entry : GetterScalar.Map) :
    Preserves (Holds selected entry) (sendKeepalive selected) := by
  apply retained selected entry _
  intro initial g a result final b pre run
  have step:=GetterScalar.rich_retained
    (Index.StagingRich.sendKeepalive_rich selected g g a result final b
      (Index.StagingRich.refl g) run)
  intro pid value present
  exact pre pid value (step pid value present)

theorem contracts (selected : PeerId) (entry : GetterScalar.Map) :
    CommandScalarRules.Contracts (Holds selected entry) selected where
  readDevice:=read_device _
  readPeer:=read_peer _ selected
  writePeer:=write selected entry
  put:=fun peer=>retained selected entry _ (fun initial=>GetterScalar.peer_put initial peer)
  remove:=fun peer=>retained selected entry _ (fun initial=>GetterScalar.remove initial peer)
  endpoint:=endpoint selected entry
  replace:=frame selected entry _ (GetterScalar.scalar_frame (ScalarAllowed.remove_frame selected))
  allowed:=fun ip=>frame selected entry _ (GetterScalar.scalar_frame (ScalarAllowed.allowed_frame selected ip))
  keepalive:=keepalive selected entry
  staged:=staged selected entry

theorem update (selected : PeerId) (entry : GetterScalar.Map)
    (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) :
    Preserves (Holds selected entry)
      (Configuration.peerConfigUpdateSource attrs peer flags psk selected) :=
  CommandScalarRules.update (contracts selected entry) attrs peer flags psk

theorem creation (key : Key) (psk : Option Key) (d : Device)
    (g final : WGWorld) (a b : Ambient) (result : Except Int PeerId)
    (device : g.dev=some d)
    (run : ((peerCreate key psk).run g).run a=.ok ((result,final),b)) :
    match result with
    | .error _=>GetterScalar.view final=GetterScalar.view g
    | .ok pid=>pid=d.nextPeer ∧ ExceptAt pid (GetterScalar.view g) (GetterScalar.view final) := by
  have effect:=Index.peerCreate_owner_fields key psk d g a result final b device run
  cases result with
  | error code=>simp only [GetterScalar.view,effect,device]
  | ok pid=>
    obtain ⟨current,p,present,footprint,_⟩:=effect
    have geometry:=peerCreate_geometry key psk g final (.ok pid) a b run
    have slot:d.nextPeer=pid:=by
      simpa only [device,Option.map_some,Option.some.injEq] using geometry.2.2
    refine ⟨slot.symm,?_⟩
    intro target value different found
    simpa only [GetterScalar.view,GetterScalar.values,present,device,Option.bind_some,
      footprint.2.2 target different] using found

theorem existing_command_rule (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid))
    (Q : Int → WGWorld → Prop)
    (following : ∀ p,before.peers[pid]?=some p → 0<p.refcount →
      Ensures (Configuration.peerConfigUpdateSource attrs (some pid)
        (attrs.flags.getD 0) attrs.presharedKey pid)
        (fun g=>Index.ConfigurationIndex.Acquired cs loans (some pid) g ∧
          g.dev=some (withPeer before pid {p with refcount:=p.refcount+1})) Q) :
    Ensures (setPeerCmd attrs)
      (fun g=>Index.ConfigurationIndex.Entry cs loans g ∧ g.dev=some before) Q := by
  intro g a result final b pre run
  obtain ⟨p,resident,positive⟩:=QueuedRemove.lookup_target_index cs loans key pid before g
    pre.1 pre.2 found
  obtain ⟨first,cut⟩:=QueuedRemove.command_lookup_default_cut attrs key pubkey
    valid protocol g final a b result run
  rw [MaterialOrigin.bind_ok_ambient] at cut
  obtain ⟨peer,u,c,looked,tail⟩:=cut
  have selected:=((ensures_iff _ _ _).mpr
    (pubkeyLookup_present key pid before p found resident positive))
      g first peer u c pre.2 looked
  obtain ⟨rfl,device⟩:=selected
  have acquired:=Index.ConfigurationIndex.lookup cs loans key
    g first (some pid) u c pre.1 looked
  change ((Configuration.peerConfigUpdateSource attrs (some pid) (attrs.flags.getD 0)
    attrs.presharedKey pid).run u).run
      (CounterWindow.record c .peerNotFound false)=.ok ((result,final),b) at tail
  exact following p resident positive u _ result final b ⟨acquired,device⟩ tail

theorem existing_command (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Ensures (setPeerCmd attrs)
      (fun g=>Index.ConfigurationIndex.Entry cs loans g ∧ g.dev=some before)
      (fun _ g=>Holds pid (GetterScalar.values (some before)) g) := by
  apply existing_command_rule cs loans attrs key pid before pubkey valid protocol found
  intro p resident _ g a result final b pre run
  have same:GetterScalar.view g=GetterScalar.values (some before):=by
    change GetterScalar.values g.dev=_
    rw [pre.2]
    exact GetterScalar.write_values before pid p {p with refcount:=p.refcount+1} resident rfl
  exact (hoare_iff_run_ambient _ _ _).mp
    (update pid (GetterScalar.values (some before)) attrs (some pid)
      (attrs.flags.getD 0) attrs.presharedKey) g a result final b
      (fun target value _ present=>by simpa only [same] using present) run

theorem missing_command (attrs : PeerAttrs) (key : Key) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (missing : before.peerHashtable.find? (·.1 == key)=none) :
    Ensures (setPeerCmd attrs) (fun g=>g.dev=some before)
      (fun _ g=>Holds before.nextPeer (GetterScalar.values (some before)) g) := by
  intro g a result final b device run
  obtain ⟨first,cut⟩:=QueuedRemove.command_lookup_default_cut attrs key pubkey
    valid protocol g final a b result run
  rw [MaterialOrigin.bind_ok_ambient] at cut
  obtain ⟨peer,u,c,looked,tail⟩:=cut
  simp [pubkeyLookup,getDev,device,missing,peerGetMaybeZero,branch,AmbientM.branch] at looked
  obtain ⟨⟨rfl,rfl⟩,rfl⟩:=looked
  apply (hoare_iff_run_ambient _ _ _).mp
    (CreationScalar.acquired_none_rule attrs key (attrs.flags.getD 0)
      (fun w=>w.dev=some before)
      (fun _ w=>Holds before.nextPeer (GetterScalar.values (some before)) w)
      (read_device _) ?_ ?_) g _ result final b device tail
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient ret out after present quiet
    change Except.ok ((0,w),CounterWindow.record (CounterWindow.record ambient .peerPutNull true)
      .peerZeroPsk attrs.presharedKey.isSome)=.ok ((ret,out),after) at quiet
    cases quiet
    intro pid value _ found
    simpa only [GetterScalar.view,present] using found
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient ret out after present actual
    rw [MaterialOrigin.bind_ok_ambient] at actual
    obtain ⟨created,middle,next,born,suffix⟩:=actual
    have fields:=creation key attrs.presharedKey before w middle ambient next created present born
    cases created with
    | error code=>
      change Except.ok ((code,middle),CounterWindow.record
        (CounterWindow.record (CounterWindow.record next .peerCreateErr true) .peerPutNull true)
        .peerZeroPsk attrs.presharedKey.isSome)=.ok ((ret,out),after) at suffix
      cases suffix
      intro pid value _ found
      have original : GetterScalar.view w pid=some value :=
        (congrFun fields pid).symm.trans found
      simpa only [GetterScalar.view,present] using original
    | ok pid=>
      obtain ⟨slot,kept⟩:=fields
      subst pid
      change ((peerGet before.nextPeer >>= fun _=>
        Configuration.peerConfigUpdateSource attrs (some before.nextPeer)
          (attrs.flags.getD 0 &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS)
          attrs.presharedKey before.nextPeer).run middle).run
        (CounterWindow.record next .peerCreateErr false)=.ok ((ret,out),after) at suffix
      rw [MaterialOrigin.bind_ok_ambient] at suffix
      obtain ⟨ignored,held,clock,acquired,updated⟩:=suffix
      have same:GetterScalar.view held=GetterScalar.view middle:=
        (ProjectedAction.iff_run_ambient _ _ _).mp (acquire before.nextPeer)
          middle _ ignored held clock acquired
      have prior:Holds before.nextPeer (GetterScalar.values (some before)) held:=by
        intro target value other found
        have earlier:GetterScalar.view middle target=some value:=by
          simpa only [same] using found
        simpa only [GetterScalar.view,present] using kept target value other earlier
      exact (hoare_iff_run_ambient _ _ _).mp
        (update before.nextPeer (GetterScalar.values (some before)) attrs (some before.nextPeer)
          (attrs.flags.getD 0 &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS) attrs.presharedKey)
        held clock ret out after prior updated

theorem remove_update (entry : GetterScalar.Map) (attrs : PeerAttrs)
    (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0) :
    Ensures (Configuration.peerConfigUpdateSource attrs peer flags psk pid)
      (GetterScalar.Retained entry) (fun _=>GetterScalar.Retained entry) := by
  intro g a result final b pre run
  have yes:(flags &&& WGPEER_F_REMOVE_ME !=0)=true:=by simpa only [bne_iff_ne] using remove
  simp only [Configuration.peerConfigUpdateSource,yes] at run
  change ((do peerRemove peer; peerPut peer
              _ ←branch .peerZeroPsk attrs.presharedKey.isSome
              pure (0 : Int) : WG.M Int).run g).run
    (CounterWindow.record a .peerRemoveMe true)=.ok ((result,final),b) at run
  have cleanup : Preserves (GetterScalar.Retained entry) (do
      peerRemove peer
      peerPut peer
      _ ←branch .peerZeroPsk attrs.presharedKey.isSome
      pure (0 : Int) : WG.M Int) := by
    repeat' first
      | (rx_retention_head peerRemove; exact (ensures_iff _ _ _).mp (GetterScalar.remove entry _))
      | (rx_retention_head peerPut; exact (ensures_iff _ _ _).mp (GetterScalar.peer_put entry _))
      | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
      | rx_retention_step
  exact (hoare_iff_run_ambient _ _ _).mp cleanup g _ result final b pre run

theorem existing_remove_command (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid))
    (remove : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME ≠ 0) :
    Ensures (setPeerCmd attrs)
      (fun g=>Index.ConfigurationIndex.Entry cs loans g ∧ g.dev=some before)
      (fun _=>GetterScalar.Retained (GetterScalar.values (some before))) := by
  apply existing_command_rule cs loans attrs key pid before pubkey valid protocol found
  intro p resident _ g a result final b pre run
  have same:GetterScalar.view g=GetterScalar.values (some before):=by
    change GetterScalar.values g.dev=_
    rw [pre.2]
    exact GetterScalar.write_values before pid p {p with refcount:=p.refcount+1} resident rfl
  exact remove_update (GetterScalar.values (some before)) attrs (some pid)
    (attrs.flags.getD 0) attrs.presharedKey pid remove g a result final b
      (fun target value present=>by simpa only [same] using present) run

theorem missing_remove_run (attrs : PeerAttrs) (key : Key) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (missing : before.peerHashtable.find? (·.1 == key)=none)
    (remove : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME≠0)
    (g final : WGWorld) (a b : Ambient) (ret : Int) (device : g.dev=some before)
    (run : ((setPeerCmd attrs).run g).run a=.ok ((ret,final),b)) :
    ret=0 ∧ final=g := by
  have blocked:=remove_blocks (attrs.flags.getD 0) remove
  obtain ⟨first,cut⟩:=QueuedRemove.command_lookup_default_cut attrs key pubkey
    valid protocol g final a b ret run
  rw [MaterialOrigin.bind_ok_ambient] at cut
  obtain ⟨peer,u,c,looked,tail⟩:=cut
  simp [pubkeyLookup,getDev,device,missing,peerGetMaybeZero,branch,AmbientM.branch] at looked
  obtain ⟨⟨rfl,rfl⟩,rfl⟩:=looked
  simp [peerCommandAcquiredWith,blocked,branch,AmbientM.branch,peerPut] at tail
  exact ⟨tail.1.1.symm,tail.1.2.symm⟩

/-- Only the actual selected slot can change a surviving serialized scalar cell.
The quiet arm permits deletions and work; the missing arm does not assert birth. -/

theorem command (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs) (before : Device) :
    Ensures (setPeerCmd attrs)
      (fun g=>Index.ConfigurationIndex.Entry cs loans g ∧ g.dev=some before)
      (fun _ g=>CommandEffect attrs before (GetterScalar.view g)) := by
  intro g a ret final b pre run
  cases validation : UpdateOnly.validationError attrs with
  | some code=>
    obtain ⟨clock,refused⟩:=UpdateOnly.validation_run attrs code validation g a
    rw [run] at refused
    cases refused
    exact CommandEffect.quiet (by simpa only [GetterScalar.view,pre.2] using
      (fun (pid : PeerId) (value : GetterScalar.Cell) (present : GetterScalar.view g pid=some value)=>present))
  | none=>
    obtain ⟨key,pubkey,valid,protocol⟩:=accepted_fields attrs validation
    cases selected : before.peerHashtable.find? (·.1 == key) with
    | none=>
      by_cases keep : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME=0
      · exact CommandEffect.missing key pubkey valid protocol keep selected
          (missing_command attrs key before pubkey valid protocol selected g a ret final b pre.2 run)
      · obtain ⟨_,same⟩:=missing_remove_run attrs key before pubkey valid protocol selected
          keep g final a b ret pre.2 run
        apply CommandEffect.quiet
        intro pid value present
        simpa only [GetterScalar.view,same,pre.2] using present
    | some pair=>
      have predicate:=List.find?_some selected
      have keyEq:pair.1=key:=by simpa only [beq_iff_eq] using predicate
      rcases pair with ⟨actual,pid⟩
      dsimp only at keyEq
      subst actual
      by_cases keep : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME=0
      · obtain ⟨p,resident,_⟩:=QueuedRemove.lookup_target_index cs loans key pid before g
          pre.1 pre.2 selected
        exact CommandEffect.existing key pid p pubkey valid protocol keep selected resident
          (existing_command cs loans attrs key pid before pubkey valid protocol selected
            g a ret final b pre run)
      · exact CommandEffect.quiet
          (existing_remove_command cs loans attrs key pid before pubkey valid protocol selected
            keep g a ret final b pre run)

end Leanux.Proofs.WG.Config.GetterScalar.Other
