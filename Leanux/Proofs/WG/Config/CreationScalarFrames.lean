import Leanux.Proofs.WG.Config.PeerScalarRetentionFrames
import Leanux.Proofs.WG.Config.CreationScalarEffects
import Leanux.Proofs.WG.Config.GetterPeerCommandFrames

/-! Selected scalar transport through original peer writes, cache/precomputation, timestamp reset and strict acquisition. These preserve the full endpoint, including cache-source fields. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.CreationScalar
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing Std.Do Queues Queues.RxCredits
open PeerScalarRetention Leanux.Proofs.WG.Configuration

theorem resident (g : WGWorld) (pid : PeerId) (expected : Cell)
    (present : view g pid=some expected) :
    ∃d p,g.dev=some d ∧ d.peers[pid]?=some p ∧ cell p=expected := by
  cases device : g.dev with
  | none=>simp [view,peerValues,device] at present
  | some d=>
    cases stored : d.peers[pid]? with
    | none=>simp [view,peerValues,device,stored] at present
    | some p=>exact ⟨d,p,rfl,stored,by simpa [view,peerValues,device,stored] using present⟩

theorem modify_selected (pid : PeerId) (f : Peer→Peer) (before after : Cell)
    (effect : ∀p,cell p=before→cell (f p)=after) :
    Hoare (modifyPeer pid f) (fun g=>view g pid=some before)
      (fun _ g=>view g pid=some after) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  obtain ⟨d,p,device,stored,same⟩:=resident g pid before pre
  have found : Noise.peerAt g pid=some p := by simp only [Noise.peerAt,device,Option.bind_some,stored]
  have kept := (Noise.ensures_iff _ _ _).mpr (modifyPeer_exact_spec pid f p)
    g a result final b found run
  change (Noise.peerAt final pid).map cell=some after
  rw [kept]
  exact congrArg some (effect p same)

theorem precompute_selected (pid : PeerId) (expected : Cell) :
    Preserves (fun g=>view g pid=some expected) (precomputeStaticStatic pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  obtain ⟨d,p,device,stored,same⟩:=resident g pid expected pre
  have original:=precomputeStaticStatic_run pid d p stored g a device
  rw [run] at original
  cases original
  simp only [view,peerValues,Option.bind_some,precomputeDevice_peer,Option.map_some]
  exact congrArg some same

theorem cache_selected (pid : PeerId) (expected : Cell) :
    Preserves (fun g=>view g pid=some expected) (dstCacheReset pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  obtain ⟨d,p,device,stored,same⟩:=resident g pid expected pre
  obtain ⟨reset,out,_⟩:=endpointReset_exact pid d p stored g.nlSock7 g.fixtureNetDevices
    g a result final b ⟨device,rfl,rfl⟩ run
  cases reset <;> simp only [view,peerValues,out,Option.bind_some,withPeer,
    Std.TreeMap.getElem?_insert_self,Option.map_some,stored]
  all_goals exact congrArg some same

theorem reset_selected (pid : PeerId) (expected : Cell) :
    Preserves (fun g=>view g pid=some expected) (resetLastSentHandshake pid) := by
  have read : Preserves (fun g=>view g pid=some expected)
      (hiddenClock64 .resetLastSent : WG.M Int64) :=
    hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent) _
  have factor : resetLastSentHandshake pid = (do
      let now ←hiddenClock64 .resetLastSent
      modifyPeer pid (fun p=>{p with lastSentHandshake:=now-(REKEY_TIMEOUT+1:Nat).toInt64*NSEC_PER_SEC64})) := rfl
  rw [factor]
  exact hoare_bind _ _ read
    (fun _=>modify_selected pid _ expected expected (fun p h=>h))

theorem peerGet_selected (pid : PeerId) (expected : Cell) :
    Preserves (fun g=>view g pid=some expected) (peerGet pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  cases result
  obtain ⟨d,p,device,stored,_,out⟩:=peerGet_loan pid g final a b run
  change g.dev=some d at device
  have before : cell p=expected:=by
    simpa only [view,peerValues,device,Option.bind_some,stored,Option.map_some,Option.some.injEq] using pre
  have after:=congrArg WGStoreView.dev out
  change final.dev=some (Index.acquirePeer d pid p) at after
  simpa only [view,peerValues,after,Option.bind_some,Index.acquirePeer,
    Std.TreeMap.getElem?_insert_self,Option.map_some,cell] using congrArg some before

end Leanux.Proofs.WG.Config.CreationScalar
