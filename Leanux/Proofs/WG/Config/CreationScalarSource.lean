import Leanux.Proofs.WG.Config.CreationScalarFrames
import Leanux.Proofs.WG.Noise.PeerCreationRuleSource
import Leanux.Proofs.WG.Noise.PeerInitializationSource

/-! Actual initialization and allocation scalar effects, including the original refusal result. No successful-run or hidden-record premise is assumed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.CreationScalar
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing Std.Do Queues Queues.RxCredits
open PeerScalarRetention Leanux.Proofs.WG.Configuration

theorem initialize_selected (pid : PeerId) (psk : Option Key) (expected : Cell) :
    Hoare (handshakeInit pid psk) (fun g=>view g pid=some expected)
      (fun _ g=>view g pid=some (initCell psk expected)) := by
  rw [handshakeInit_source]
  apply hoare_bind _ _ (modify_selected pid (fun p=>{p with handshakeEntryPeer:=some pid}) expected expected (fun p h=>h))
  intro _
  cases psk with
  | none=>
    change Hoare (do _ ←branch .handshakeInitHasPsk false; precomputeStaticStatic pid)
      (fun g=>view g pid=some expected) (fun _ g=>view g pid=some (initCell none expected))
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .handshakeInitHasPsk false) _)
    intro _
    exact precompute_selected pid expected
  | some key=>
    change Hoare (do _ ←branch .handshakeInitHasPsk true
                     modifyPeer pid (fun p=>{p with presharedKey:=key})
                     precomputeStaticStatic pid)
      (fun g=>view g pid=some expected) (fun _ g=>view g pid=some (initCell (some key) expected))
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .handshakeInitHasPsk true) _)
    intro _
    apply hoare_bind _ _ (modify_selected pid (fun p=>{p with presharedKey:=key}) expected (initCell (some key) expected) ?_)
    · intro _
      exact precompute_selected pid _
    · intro p h
      rw [←h]
      rfl

theorem finish_selected (pid : PeerId) (key : Key) (psk : Option Key) (expected : Cell) :
    Hoare (BaseCreation.finish pid key psk) (fun g=>view g pid=some expected)
      (fun _ g=>view g pid=some (initCell psk expected)) := by
  unfold BaseCreation.finish
  apply hoare_bind _ _ (cache_selected pid expected)
  intro _
  apply hoare_bind _ _ (initialize_selected pid psk expected)
  intro _
  apply hoare_bind _ _ (reset_selected pid (initCell psk expected))
  intro _
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  cases run
  simpa only [view,peerValues,ConfiguredIdentity.publishRow,modifyDev,Option.bind_map,Function.comp_def] using pre

theorem create_selected (key : Key) (psk : Option Key) (start : WGWorld) (d : Device)
    (device : start.dev=some d) :
    Noise.Ensures (peerCreate key psk) (fun g=>g=start)
      (fun result g=>match result with
      | .error code=>code=-ENOMEM ∧ g=start
      | .ok pid=>view g pid=some (initCell psk (newbornCell (start.peerCounter+1)))) := by
  refine (Noise.ensures_iff (peerCreate key psk) (fun g=>g=start)
    (fun result g=>match result with
    | .error code=>code=-ENOMEM ∧ g=start
    | .ok pid=>view g pid=some (initCell psk (newbornCell (start.peerCounter+1))))).mpr ?_
  apply peerCreate_rule key psk (fun g=>g=start)
    (fun pid g=>view g pid=some (newbornCell (start.peerCounter+1)))
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro g a result final b pre run
    subst g
    simp [getDev,device] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩:=run
    rfl
  · intro g pre
    exact ⟨rfl,pre⟩
  · intro pid
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro g a result final b pre run
    subst g
    rw [Peers.peerCreateCore_run] at run
    cases run
    simp only [view,peerValues,Peers.creationCoreWorld,device,Option.map_some,Option.bind_some,
      Std.TreeMap.getElem?_insert_self,Option.map_some,newbornCell,cell,Peers.createdPeer]
  · intro pid
    exact finish_selected pid key psk _

end Leanux.Proofs.WG.Config.CreationScalar
