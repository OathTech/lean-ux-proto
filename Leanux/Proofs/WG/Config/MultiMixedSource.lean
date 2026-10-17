import Leanux.Proofs.WG.Config.MultiMixedEffects
import Leanux.Proofs.WG.Config.FwmarkEffects
import Leanux.Proofs.WG.Config.PortRefusalFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Normal effects of the complete mixed request on an arbitrary peer list.
Missing listed peers and cache reset records remain actual Stops. -/
theorem setDevice_multi_mixed (d : Device) (mark : Nat) (key psk : Key)
    (interval : Nat) (bad : Bool) (pid : PeerId) (p : Peer)
    (sock : NlSock) (fixtures : FixtureDevices)
    (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures ∧ selectsDevice g d)
      (fun ret g => ret = (if bad then -EINVAL else 0) ∧ readbackFrame g sock fixtures ∧
        ∃ final, g.dev = some final ∧ MultiMixedEffect d mark pid psk interval final) := by
  let updated := mixedFwmarkBase d mark
  let P : WGWorld → Prop := fun g => g.dev.map withoutPeers = some (withoutPeers updated) ∧
    clearedPeers d g d.peerList ∧ readbackFrame g sock fixtures
  let Q : Int → WGWorld → Prop := fun ret g => ret = (if bad then -EINVAL else 0) ∧
    readbackFrame g sock fixtures ∧ ∃ final, g.dev = some final ∧ MultiMixedEffect d mark pid psk interval final
  let tail : WG.M Int := do
    _ ← branch .setDevFwmarkPeerIter false
    _ ← branch .setDevPort false
    _ ← branch .setDevReplacePeers false
    _ ← branch .setDevHasPrivateKey false
    devicePeersSource (mixedFwmarkAttrs d mark key psk interval bad)
  have peerSource : devicePeersSource (mixedFwmarkAttrs d mark key psk interval bad) =
      devicePeersSource (scalarDeviceAttrs d key psk interval bad) := rfl
  have finish : Ensures tail P Q := by
    intro g a ret final after pre run
    obtain ⟨current,device,outer⟩ := Option.map_eq_some_iff.mp pre.1
    have clears : ClearedPeerStore d current d.peerList := by
      simpa only [ClearedPeerStore,clearedPeers,device,Option.bind_some] using pre.2.1
    obtain ⟨selected,selectedResident,shape⟩ :=
      clearedPeerStore_resident d current d.peerList clears pid p resident
    have count : selected.refcount = p.refcount := by
      rcases shape with rfl | ⟨reset,rfl⟩ <;> rfl
    have sameTable : current.peerHashtable = d.peerHashtable := by
      have h := congrArg Device.peerHashtable outer
      exact h
    have sameRun : current.running = d.running := by
      have h := congrArg Device.running outer
      exact h
    have hf : current.peerHashtable.find? (·.1 == key) = some (key,pid) := by rw [sameTable]; exact found
    have hl : 0 < selected.refcount := by simpa only [count] using live
    have hb : selected.refcount + 1 < 2 ^ 31 := by simpa only [count] using bounded
    let start := {a with steps := (((a.steps.push {
      decision := .setDevFwmarkPeerIter, outcome := false, netRx := a.netRxSection}).push {
      decision := .setDevPort, outcome := false, netRx := a.netRxSection}).push {
      decision := .setDevReplacePeers, outcome := false, netRx := a.netRxSection}).push {
      decision := .setDevHasPrivateKey, outcome := false, netRx := a.netRxSection}}
    obtain ⟨value,out,rest,executed,code,changed,framed⟩ :=
      (returns_iff _ _ _).mpr
        (devicePeers_scalars_framed d current key psk interval bad pid selected sock fixtures
          hf selectedResident hl hb (sameRun.trans down)) g start ⟨device,pre.2.2⟩
    have source : (tail.run g).run a =
        ((devicePeersSource (scalarDeviceAttrs d key psk interval bad)).run g).run start := by
      simp [tail,peerSource,branch,AmbientM.branch,start]
    rw [source,executed] at run
    cases run
    exact ⟨code,framed,_,changed,current,selected,outer,clears,selectedResident,rfl⟩
  have whole : Ensures (do fwmarkClearLoop d.peerList; tail)
      (fun g => g.dev = some updated ∧ readbackFrame g sock fixtures) Q := by
    refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => finish)
    intro g a value final after pre run
    have effects := fwmarkClearLoop_effects d d.peerList [] (some (withoutPeers updated))
      g a value final after (by simp [clearedPeers,pre.1,updated,mixedFwmarkBase]) run
    have saved := endpointClearLoop_configurationFrame .setDevFwmarkPeerIter d.peerList
      g.portBound sock fixtures g a value final after ⟨rfl,pre.2⟩ run
    exact ⟨effects.1,effects.2,saved.2⟩
  intro g a ret final after pre run
  obtain ⟨value,middle,next,lookupRun,lookupValue,device,framed⟩ :=
    (returns_iff _ _ _).mpr (lookupInterface_index_framed d sock fixtures) g a pre
  subst value
  let logged (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site,outcome := value,netRx := a.netRxSection}}
  let before := logged (logged (logged (logged (logged (logged (logged (logged (logged next
    .setDevLookupErr false) .setDevHasFlags false) .setDevBadFlags false)
    .setDevHasPort false) .setDevHasFwmark true) .setDevNoNet false)
    .setDevNotCapable false) .setDevPermErr false) .setDevFwmark true
  have source : ((wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)).run g).run a =
      (((do fwmarkClearLoop d.peerList; tail) : WG.M Int).run {middle with dev := some updated}).run before := by
    rw [← wgSetDevice_source]
    simp only [wgSetDeviceSource,← deviceUpdate_loop_factor]
    simp [mixedFwmarkAttrs,scalarDeviceAttrs,WG.orM,branch,AmbientM.branch,WGDEVICE_F_ALL]
    rw [show ((lookupInterface (byIndex d)).run g).run a = .ok ((.ok (),middle),next) from lookupRun]
    dsimp only [bind,Except.bind]
    simp [deviceFwmarkUpdateSource,deviceKeySource,WG.andM,branch,AmbientM.branch,
      getDev,device,net,modifyDev,WGDEVICE_F_REPLACE_PEERS,tail,fwmarkClearLoop,
      mixedFwmarkAttrs,scalarDeviceAttrs,updated,mixedFwmarkBase,before,logged,
      StateT.run,StateT.bind,StateT.lift,StateT.pure,Except.bind,Except.pure,
      liftM,monadLift,pure,bind,get,modify,modifyGet,MonadLift.monadLift,
      MonadStateOf.modifyGet,getThe,StateT.modifyGet,MonadStateOf.get,StateT.get,Functor.map,StateT.map]
  exact whole {middle with dev := some updated} before ret final after ⟨rfl,framed⟩ (source.symm.trans run)


end Leanux.Proofs.WG.Config
