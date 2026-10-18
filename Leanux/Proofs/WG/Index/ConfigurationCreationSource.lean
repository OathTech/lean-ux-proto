import Leanux.Proofs.WG.Index.ConfigurationPeerSource
import Leanux.Proofs.WG.Index.CreationIndexClaims
import Leanux.Proofs.WG.Index.OwnerCoherencePeerCreateClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

theorem creation_core (key : Key) (psk : Option Key) :
    Ensures (peerCreate key psk) (fun w=>ConfiguredIdentity.Inv w ∧ Reached.Core w)
      (fun _=>Reached.Core) := by
  intro w a result v b pre run
  have coherent := (peerCreate_owner_coherent key psk w a result v b
    (fun d hd=>(pre.2 d hd).2.2.1) run).1
  have structural := peerCreate_hashSlots_retirement_source key psk [] w a result v b
    ⟨pre.1,fun d hd=>(pre.2 d hd).2.1,fun d hd=>(pre.2 d hd).2.2.2⟩ run
  intro current final
  have geometry := peerCreate_geometry key psk w v result a b run
  obtain ⟨d,device,_,cursor,_,_⟩ := geometry.device final
  have effect := peerCreate_owner_fields key psk d w a result v b device run
  have table : current.indexTable=d.indexTable := by
    cases result with
    | error code =>
      have same : current=d := Option.some.inj (final.symm.trans effect)
      exact same ▸ rfl
    | ok pid =>
      obtain ⟨e,p,out,footprint,_⟩ := effect
      have same : current=e := Option.some.inj (final.symm.trans out)
      exact same ▸ footprint.1
  have before := (pre.2 d device).1
  exact ⟨⟨table ▸ before.1,table ▸ before.2.1,
    fun entry member kid owner=>cursor ▸ before.2.2 entry (table ▸ member) kid owner⟩,
    structural.1 current final,coherent current final,structural.2 current final⟩

theorem creation_entry (cs : Ledger) (loans : Reservations) (key : Key) (psk : Option Key) :
    Preserves (Entry cs loans) (peerCreate key psk) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  have core := creation_core key psk w a result v b ⟨pre.1.2.2,pre.2.2⟩ run
  have slots := (hoare_iff_run_ambient _ _ _).mp
    (CurrentSlots.peerCreate_preserves key psk) w a result v b pre.2.1 run
  obtain ⟨holders,funded,stable⟩ := pre.1.1
  have post := CreationLoan.creation key psk funded stable pre.1.2.1 pre.1.2.2 a b run
  refine ⟨⟨?_,post.1,post.2.1⟩,slots,core⟩
  cases result with
  | error code=>exact ⟨holders,post.2.2⟩
  | ok pid=>
    obtain ⟨d,_,_,after,stableOut⟩ := post.2.2
    exact ⟨HolderCreation.addBase holders (BaseCreation.owner w d),after,stableOut⟩

theorem acquire_core (pid : PeerId) : Preserves Reached.Core (peerGet pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases result
  obtain ⟨d,p,device,resident,_,out⟩ := peerGet_loan pid w v a b run
  have target : v.dev=some (acquirePeer d pid p) := congrArg WGStoreView.dev out
  intro e final
  have same : e=acquirePeer d pid p := Option.some.inj (final.symm.trans target)
  exact same ▸ deviceIndexCore_acquire d pid p resident (pre d device)

/-- Actual successful creation and its immediately following recorded strict
acquisition. This source cut obtains the new base and loan from the landed
account theorem and transports slots/Core through those same two executions. -/
theorem creation_acquire_entry (cs : Ledger) (loans : Reservations) (key : Key) (psk : Option Key)
    (w u v : WGWorld) (a middle b : Ambient) (pid : PeerId)
    (pre : Entry cs loans w)
    (create : ((peerCreate key psk).run w).run a=.ok ((.ok pid,u),middle))
    (acquire : ((peerGet pid).run u).run (CounterWindow.record middle .peerCreateErr false)=.ok (((),v),b)) :
    Acquired cs loans (some pid) v := by
  have created := (hoare_iff_run_ambient _ _ _).mp
    (creation_entry cs loans key psk) w a (.ok pid) u middle pre create
  have slots := (hoare_iff_run_ambient _ _ _).mp
    (CurrentSlots.fields_preserves (project:=id) (CurrentSlots.peerGet_fields pid))
    u _ () v b created.2.1 acquire
  have core := (hoare_iff_run_ambient _ _ _).mp (acquire_core pid)
    u _ () v b created.2.2 acquire
  obtain ⟨holders,funded,stable⟩ := pre.1.1
  obtain ⟨d,device,selected,fundedOut,stableOut,base,configured,member⟩ :=
    CreationLoan.creation_acquire key psk funded stable pre.1.2.1 pre.1.2.2 a middle b create acquire
  refine ⟨BaseCreation.owner w d,selected.symm,?_,member⟩
  exact ⟨⟨⟨HolderCreation.addBase holders (BaseCreation.owner w d),fundedOut,stableOut⟩,
    base,configured⟩,slots,core⟩

end Leanux.Proofs.WG.Index.ConfigurationIndex
