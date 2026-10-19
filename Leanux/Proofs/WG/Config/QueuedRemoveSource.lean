import Leanux.Proofs.WG.Config.QueuedRemoveModel
import Leanux.Proofs.WG.Config.ConfiguredCommandClaims
import Leanux.Proofs.WG.Config.PeerScalars
import Leanux.Proofs.WG.Config.ConfiguredRepresentationEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.QueuedRemove
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration

/-- Exact existing detach effects, projected to the configured list/table. -/
theorem makeDead_base (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((peerMakeDead pid).run w).run a=.ok (((),v),b)) :
    BaseCoherence.slots v=(BaseCoherence.slots w).filter (· != pid) ∧
    BaseCoherence.rows v=(BaseCoherence.rows w).filter (·.2 != pid) := by
  have list := congrArg (fun s : Option (List PeerId) => s.getD [])
    (BaseRemoval.peerMakeDead_normal pid w v a b run).2
  have table := congrArg (fun s : Option ConfiguredIdentity.State =>
    (s.map ConfiguredIdentity.State.rows).getD [])
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherence.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.makeDead_configured)
      pid w v a b run)
  constructor
  · cases hd : w.dev <;> simpa [BaseCoherence.slots,hd] using list
  · cases hd : w.dev <;>
      simpa [BaseCoherence.rows,ConfiguredIdentity.view,ConfiguredIdentity.state,
        ConfiguredIdentity.State.kill,Option.map_map,Function.comp_def,hd] using table

/-- The complete native removal keeps the original queued cleanup. -/
theorem remove_base (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((peerRemove (some pid)).run w).run a=.ok (((),v),b)) :
    BaseCoherence.slots v=(BaseCoherence.slots w).filter (· != pid) ∧
    BaseCoherence.rows v=(BaseCoherence.rows w).filter (·.2 != pid) := by
  change ((peerMakeDead pid >>= fun _=>peerRemoveAfterDead pid).run w).run
    (CounterWindow.record a .peerRemoveNull false)=.ok (((),v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,u,c,dead,cleanup⟩ := run
  cases ignored
  have detached := makeDead_base pid w u _ c dead
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (BaseCoherence.afterDead_view pid) u c () v b cleanup
  exact ⟨(congrArg Prod.fst same).trans detached.1,
    (congrArg Prod.snd same).trans detached.2⟩

theorem effect_of_entry (cs : Ledger) (loans : Reservations)
    (before after : Device) (pid : PeerId) (g : WGWorld)
    (device : g.dev=some after) (entry : Entry cs loans g)
    (list : after.peerList=before.peerList.filter (· != pid))
    (table : after.peerHashtable=before.peerHashtable.filter (·.2 != pid)) :
    Effect before pid after := by
  refine ⟨list,table,?_⟩
  intro t4 t6 routing e member
  obtain ⟨old,present,u4,u6,represented,owners⟩ := entry.2
  have eq : old=after := Option.some.inj (present.symm.trans device)
  subst old
  have owners := configuredOwners_representation after u4 u6 t4 t6
    represented.forest routing.forest owners
  have listed := owners e member
  rw [list] at listed
  have different := (List.mem_filter.mp listed).2
  simpa only [bne_iff_ne] using different

/-- Removal takes precedence over every later field, including malformed IPs.
The selected loan is paid after the complete original drains. -/
theorem update (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0) (before : Device) :
    Ensures (peerConfigUpdateSource attrs (some paid.slot) flags psk paid.slot)
      (fun g=>SelectedEntry cs (paid::loans) paid.slot g ∧ g.dev=some before)
      (fun ret g=>ret=0 ∧ Entry cs loans g ∧
        ∃ after,g.dev=some after ∧ Effect before paid.slot after) := by
  intro w a result v b pre run
  have shapeFree := Index.ConfigurationIndex.removeMe cs loans paid attrs flags psk
    (by simpa only [bne_iff_ne] using remove) w a result v b
    ⟨pre.1.1.1,pre.1.2⟩ run
  rw [peerUpdate_remove_source attrs (some paid.slot) flags psk paid.slot remove] at run
  change ((do peerRemove (some paid.slot); peerPut (some paid.slot)
              _ ← branch .peerZeroPsk attrs.presharedKey.isSome
              pure (0 : Int) : WG.M Int).run w).run
    (CounterWindow.record a .peerRemoveMe true)=.ok ((result,v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,u,c,removed,tail⟩ := run
  cases ignored
  have current := remove_entry cs (paid::loans) paid.slot w _ () u c pre.1 removed
  have detached := remove_base paid.slot w u _ c removed
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨ignored,z,d,payment,done⟩ := tail
  cases ignored
  have ready := (hoare_iff_run_ambient _ _ _).mp
    (retained_ready _ (peerPut_retainsRouting (some paid.slot))
      (BaseCoherence.peerPut_view (some paid.slot))) u c () z d current.2 payment
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (BaseCoherence.peerPut_view (some paid.slot)) u c () z d payment
  change Except.ok ((0,z),CounterWindow.record d .peerZeroPsk attrs.presharedKey.isSome)=
    .ok ((result,v),b) at done
  cases done
  have entry : OwnerConfiguration.Entry cs loans v := ⟨shapeFree.2,ready⟩
  obtain ⟨after,device,_⟩ := ready
  have list : after.peerList=before.peerList.filter (· != paid.slot) := by
    simpa only [BaseCoherence.view,BaseCoherence.slots,device,pre.2,Option.map_some,Option.getD_some]
      using (congrArg Prod.fst same).trans detached.1
  have table : after.peerHashtable=before.peerHashtable.filter (·.2 != paid.slot) := by
    simpa only [BaseCoherence.view,BaseCoherence.rows,device,pre.2,Option.map_some,Option.getD_some]
      using (congrArg Prod.snd same).trans detached.2
  exact ⟨rfl,entry,after,device,effect_of_entry cs loans before after paid.slot v device entry list table⟩

/-- A configured lookup target's actual base occurrence supplies residency
and a positive reference; no numeric slack is assumed. -/
theorem lookup_target_index (cs : Ledger) (loans : Reservations) (key : Key)
    (pid : PeerId) (d : Device) (g : WGWorld)
    (entry : Index.ConfigurationIndex.Entry cs loans g) (device : g.dev=some d)
    (found : d.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    ∃ p,d.peers[pid]?=some p ∧ 0<p.refcount := by
  have row : (key,pid)∈d.peerHashtable := List.mem_of_find?_eq_some found
  have member : pid∈d.peerList := by
    have h := entry.1.2.1.2 (key,pid)
      (by simpa only [BaseCoherence.rows,device,Option.map_some,Option.getD_some] using row)
    simpa only [BaseCoherence.slots,device,Option.map_some,Option.getD_some] using h
  obtain ⟨holders,funded,_⟩ := entry.1.1
  have mapped : pid∈holders.base.map Owner.slot := by
    rw [funded.aligned.base]
    simpa only [device,Option.map_some,Option.getD_some] using member
  obtain ⟨owner,inside,slot⟩ := List.mem_map.mp mapped
  have held : owner∈holders.owners := by
    simp only [DurableHolders.owners,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl inside))))
  have demandPos : 0<demand cs (holders.owners++loans) owner := by
    have count := List.count_pos_iff.mpr held
    simp only [demand,List.count_append]
    omega
  obtain ⟨p,stored,bound⟩ := protected_resident funded.carriers.funded demandPos
  obtain ⟨actual,current,_,resident,_⟩ := resident_fields stored
  rw [device] at current
  cases current
  exact ⟨p,by simpa only [slot] using resident,by omega⟩

theorem lookup_target (cs : Ledger) (loans : Reservations) (key : Key)
    (pid : PeerId) (d : Device) (g : WGWorld)
    (entry : Entry cs loans g) (device : g.dev=some d)
    (found : d.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    ∃ p,d.peers[pid]?=some p ∧ 0<p.refcount :=
  lookup_target_index cs loans key pid d g entry.1 device found
/-- The original validating header leads to this same-call lookup/acquired
suffix, with the existing source factory and an unchanged WG state. -/
theorem command_lookup_default_cut (attrs : PeerAttrs) (key : Key)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (g v : WGWorld) (a b : Ambient) (result : Int)
    (run : ((setPeerCmd attrs).run g).run a=.ok ((result,v),b)) :
    ∃ first,
      ((do let peer ← pubkeyLookup key
           peerCommandAcquiredWith (fun {_} action=>action) peerCreate peerGet
             (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
             (Configuration.peerConfigUpdateSource attrs) key attrs.presharedKey (attrs.flags.getD 0) peer).run g).run first
        =.ok ((result,v),b) := by
  rw [←Configuration.setPeerCmd_source,Configuration.setPeerCmdSource_factor] at run
  rcases protocol with protocol | protocol
  all_goals cases psk : attrs.presharedKey
  all_goals cases flags : attrs.flags
  all_goals simp only [flags,Option.getD_none,Option.getD_some] at valid
  all_goals simp [setPeerCmdWith,pubkey,flags,valid,protocol,psk,
    WG.andM,branch,AmbientM.branch] at run
  all_goals exact ⟨_,by simpa [psk,flags,branch,AmbientM.branch] using run⟩

/-- The original explicit-flags cut is retained as an exact-type adapter. -/
theorem command_lookup_cut (attrs : PeerAttrs) (key : Key) (flags : UInt32)
    (pubkey : attrs.publicKey=some key) (flagattr : attrs.flags=some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (g v : WGWorld) (a b : Ambient) (result : Int)
    (run : ((setPeerCmd attrs).run g).run a=.ok ((result,v),b)) :
    ∃ first,
      ((do let peer ← pubkeyLookup key
           peerCommandAcquiredWith (fun {_} action=>action) peerCreate peerGet
             (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
             (Configuration.peerConfigUpdateSource attrs) key attrs.presharedKey flags peer).run g).run first
        =.ok ((result,v),b) := by
  have cut := command_lookup_default_cut attrs key pubkey
    (by simpa only [flagattr,Option.getD_some] using valid) protocol g v a b result run
  simpa only [flagattr,Option.getD_some] using cut

/-- The complete original command derives its selected caller from the
initial table and funded base. Every later peer attribute is bypassed. -/
theorem command (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (flags : UInt32) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key) (flagattr : attrs.flags=some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Ensures (setPeerCmd attrs)
      (fun g=>Entry cs loans g ∧ g.dev=some before)
      (fun ret g=>ret=0 ∧ Entry cs loans g ∧
        ∃ after,g.dev=some after ∧ Effect before pid after) := by
  intro g a result v b pre run
  obtain ⟨p,resident,live⟩ := lookup_target cs loans key pid before g pre.1 pre.2 found
  obtain ⟨first,cut⟩ := command_lookup_cut attrs key flags pubkey flagattr valid protocol g v a b result run
  rw [MaterialOrigin.bind_ok_ambient] at cut
  obtain ⟨peer,u,c,looked,tail⟩ := cut
  have selection := ((ensures_iff _ _ _).mpr
    (pubkeyLookup_present key pid before p found resident live)) g first peer u c pre.2 looked
  obtain ⟨rfl,device⟩ := selection
  have acquired := lookup_acquired cs loans key g first (some pid) u c pre.1 looked
  obtain ⟨⟨paid,slot,entry,member⟩,ready⟩ := acquired
  subst pid
  change ((Configuration.peerConfigUpdateSource attrs (some paid.slot) flags
    attrs.presharedKey paid.slot).run u).run
    (CounterWindow.record c .peerNotFound false)=.ok ((result,v),b) at tail
  have done := update cs loans paid attrs flags attrs.presharedKey remove
    (withPeer before paid.slot {p with refcount:=p.refcount+1})
    u _ result v b ⟨⟨⟨entry,ready⟩,member⟩,device⟩ tail
  obtain ⟨zero,entry,after,present,effect⟩ := done
  exact ⟨zero,entry,after,present,by simpa only [Effect,withPeer] using effect⟩


end Leanux.Proofs.WG.Config.QueuedRemove
