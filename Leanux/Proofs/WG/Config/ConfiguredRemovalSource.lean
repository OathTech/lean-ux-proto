import Leanux.Proofs.WG.Config.ConfiguredRemovalFrames
import Leanux.Proofs.WG.Config.ConfiguredOwnerClaims
import Leanux.Proofs.WG.Queues.BaseCoherenceRemoval

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise AllowedIps
open Leanux.Proofs.Framing Lifetimes Queues.RxCredits Std.Do

/-- Initial representation suffices. The selected peer is recovered from the
actual normal removal cut, after the original base unlink. -/
theorem peerMakeDead_configured_run (d : Device) (t4 t6 : Tree) (pid : PeerId)
    (routing : RoutingInvariant d t4 t6) (owners : ConfiguredOwners d t4 t6)
    (g : WGWorld) (ambient : Ambient) (value : Unit) (final : WGWorld) (after : Ambient)
    (device : g.dev=some d)
    (run : ((peerMakeDead pid).run g).run ambient=.ok ((value,final),after)) :
    ∃ out p, final.dev=some out ∧ d.peers[pid]?=some p ∧
      out.peerList=d.peerList.filter (· != pid) ∧
      RoutingInvariant out (t4.eraseIds p.allowedipsList) (t6.eraseIds p.allowedipsList) ∧
      ConfiguredOwners out (t4.eraseIds p.allowedipsList) (t6.eraseIds p.allowedipsList) := by
  cases value
  have listed := (BaseRemoval.peerMakeDead_normal pid g final ambient after run).2
  have source := run
  rw [peerMakeDead_source,MaterialOrigin.bind_ok_ambient] at source
  obtain ⟨u,middle,first,unlink,rest⟩ := source
  have unlinkRun : ((modifyDev (unlistPeer · pid)).run g).run ambient =
      .ok (((),{g with dev:=some (unlistPeer d pid)}),ambient) := by
    simp [modifyDev,device]
  rw [unlinkRun] at unlink
  cases unlink
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,removed,beforeMark,remove,mark⟩ := rest
  cases u
  obtain ⟨p,resident⟩ := removeByPeer_input_resident _ _ _ _ (unlistPeer d pid) pid rfl remove
  have input := routing.of_routingState (show routingState (unlistPeer d pid)=routingState d from rfl)
  obtain ⟨out,reached,inputs,actual,state,effect,representation⟩ :=
    removeByPeer_routing_total {g with dev:=some (unlistPeer d pid)} ambient (unlistPeer d pid) rfl pid p resident t4 t6 input
  cases actual.symm.trans remove
  have markFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (makeDeadAfterRemoval_routing pid) removed beforeMark () final after mark
  have atOut : removed.dev=some out := by rw [state]
  have route : routingView final=some (routingState out) := by
    simpa only [routingView,atOut,Option.map_some] using markFrame
  obtain ⟨result,present,view⟩ := Option.map_eq_some_iff.mp route
  have list : result.peerList=d.peerList.filter (· != pid) := by
    simpa only [present,device,Option.map_some,Option.some.injEq] using listed
  exact ⟨result,p,present,resident,list,representation.of_routingState view,
    configuredOwners_removed d result t4 t6 pid p resident owners routing.lists list⟩

/-- Cleanup may release peer objects; it retains the configured list and
represented tables. No funding or future-state premise is needed for this
boundary membership claim. -/
theorem peerRemoveAfterDead_configured_run (d : Device) (t4 t6 : Tree)
    (pid : PeerId) (routing : RoutingInvariant d t4 t6)
    (owners : ConfiguredOwners d t4 t6)
    (g : WGWorld) (ambient : Ambient) (value : Unit) (final : WGWorld) (after : Ambient)
    (device : g.dev=some d)
    (run : ((peerRemoveAfterDead pid).run g).run ambient=.ok ((value,final),after)) :
    ∃ out,final.dev=some out ∧ out.peerList=d.peerList ∧
      RoutingInvariant out t4 t6 ∧ ConfiguredOwners out t4 t6 := by
  have retained := (ProjectedAction.iff_run_ambient _ _ _).mp
    (peerRemoveAfterDead_routing pid) g ambient value final after run
  change RetainsRouting (routingView g) (routingView final) at retained
  have listFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (BaseCoherence.afterDead_view pid) g ambient value final after run
  cases present : final.dev with
  | none =>
    simp only [routingView,device,present,Option.map_some,Option.map_none,RetainsRouting] at retained
  | some out =>
    have view : (routingState d).Retains (routingState out) := by
      simpa only [routingView,device,present,Option.map_some,RetainsRouting] using retained
    have list : out.peerList=d.peerList := by
      simpa only [BaseCoherence.view,BaseCoherence.slots,present,device,
        Option.map_some,Option.getD_some] using congrArg Prod.fst listFrame
    exact ⟨out,rfl,list,routing.of_retains view,
      fun e member=>list.symm ▸ owners e member⟩

theorem peerRemove_configured_run (d : Device) (t4 t6 : Tree)
    (peer : Option PeerId) (routing : RoutingInvariant d t4 t6)
    (owners : ConfiguredOwners d t4 t6)
    (g : WGWorld) (ambient : Ambient) (value : Unit) (final : WGWorld) (after : Ambient)
    (device : g.dev=some d)
    (run : ((peerRemove peer).run g).run ambient=.ok ((value,final),after)) :
    ∃ out u4 u6,final.dev=some out ∧
      RoutingInvariant out u4 u6 ∧ ConfiguredOwners out u4 u6 := by
  cases value
  cases peer with
  | none =>
    simp [peerRemove,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨d,t4,t6,device,routing,owners⟩
  | some pid =>
    change ((peerMakeDead pid >>= fun _=>peerRemoveAfterDead pid).run g).run
      (CounterWindow.record ambient .peerRemoveNull false)=.ok (((),final),after) at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨u,middle,cut,makeDead,cleanup⟩ := run
    cases u
    obtain ⟨marked,p,present,_,_,represented,configured⟩ :=
      peerMakeDead_configured_run d t4 t6 pid routing owners
        g (CounterWindow.record ambient .peerRemoveNull false) () middle cut
        (show g.dev=some d from device) makeDead
    obtain ⟨out,present,_,represented,configured⟩ :=
      peerRemoveAfterDead_configured_run marked _ _ pid represented configured
        middle cut () final after present cleanup
    exact ⟨out,_,_,present,represented,configured⟩



end Leanux.Proofs.WG.Config
