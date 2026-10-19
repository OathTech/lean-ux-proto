import Leanux.Proofs.WG.Config.GetterStagingFrames
import Leanux.Proofs.WG.Queues.BaseCreation
import Leanux.Proofs.WG.Config.Precomputation
import Leanux.Proofs.WG.Config.EndpointSetSource
import Leanux.Proofs.WG.Roaming.RemoteControlFrames
import Leanux.Proofs.WG.Index.IncomingConsumeSource
import Leanux.Proofs.WG.Index.AllowedFrameSource
import Leanux.Proofs.WG.Noise.PeerInitializationSource

/-! Metadata projections of owned source effects and generic proof spines.
The endpoint projection uses the exact supported-family effect and the proved
unsupported-family no-op; it does not repeat the setter's source branches. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterPeerCommand
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do Queues
open GetterCleanup
theorem insertion_contracts : AllowedFrame.InsertionContracts getterMetadata where
  aip := aip
  deleteList := list_delete
  appendList := fun pid id=>modify_peer pid (fun p=>{p with allowedipsList:=p.allowedipsList++[id]})
  sequence := modify_device _ (fun _=>rfl)
theorem allowed (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView getterMetadata (setAllowedip pid ip) :=
  AllowedFrame.allowed_insertion insertion_contracts pid ip

theorem cache_reset (pid : PeerId) : SameView getterMetadata (dstCacheReset pid) :=
  fun initial=>(ensures_iff _ _ _).mp
    (getterMetadata_frame_of_sendWork _ pid (dstCacheReset_sendWorkView pid) initial)
theorem precompute (pid : PeerId) : SameView getterMetadata (precomputeStaticStatic pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases device : g.dev with
  | none =>
    simp [precomputeStaticStatic,requireNotPending,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [precomputeStaticStatic,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have actual := precomputeStaticStatic_run pid d p resident g ambient device
      rw [run] at actual
      cases actual
      simp only [getterMetadata,device,Option.map_some]
      unfold precomputeDevice
      split
      · dsimp only
        split <;> rfl
      · rfl
theorem handshake_init (pid : PeerId) (psk : Option Key) :
    SameView getterMetadata (handshakeInit pid psk) :=
  handshakeInit_frame_source getterMetadata pid psk
    (modify_peer pid _) (modify_peer pid _) (precompute pid)
theorem reset_last (pid : PeerId) : SameView getterMetadata (resetLastSentHandshake pid) :=
  resetLastSentHandshake_frame_source getterMetadata pid (fun _=>modify_peer pid _)
theorem create_core (pid : PeerId) (key : Key) :
    SameView getterMetadata (Peers.peerCreateCore pid key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a x final b run
  rw [Peers.peerCreateCore_run] at run
  cases run
  simp only [getterMetadata,Peers.creationCoreWorld,Option.map_map,Function.comp_def]
  rfl
theorem lookup (key : Key) : SameView getterMetadata (pubkeyLookup key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  have preserve : ∀ w d pid p,w.dev=some d → d.peers[pid]?=some p →
      getterMetadata w=getterMetadata g →
      getterMetadata {w with dev:=some (Index.acquirePeer d pid p)}=getterMetadata g := by
    intro w d pid p device _ pre
    simpa only [getterMetadata,device,Option.map_some,Index.acquirePeer,sendConfiguration] using pre
  exact (Index.pubkeyLookup_preserves_acquire_world_source key
    (fun w=>getterMetadata w=getterMetadata g) preserve g ambient result final after rfl run).1

theorem endpoint (pid : PeerId) (e : Endpoint) :
    SameView getterMetadata (setPeerEndpoint pid e) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  by_cases valid : e.family=AF_INET ∨ e.family=AF_INET6
  · have original := run
    unfold setPeerEndpoint at run
    simp only [requireNotPending,pure_bind] at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨p,current,a,read,_⟩ := run
    obtain ⟨_,_,d,device,resident⟩ := getPeer_normal pid g current p ambient a read
    obtain ⟨reset,effect,frame,_⟩ := setPeerEndpoint_exact pid e d p resident valid
      g.nlSock7 g.fixtureNetDevices g ambient result final after ⟨device,rfl,rfl⟩ original
    obtain ⟨sock,fixtures⟩ := frame
    simp only [getterMetadata,effect,device,sock,fixtures,Option.map_some]
    unfold endpointStores
    split
    · rfl
    · cases reset <;> rfl
  · exact congrArg getterMetadata ((ProjectedAction.iff_run_ambient _ _ _).mp
      (Roaming.RemoteControl.setPeerEndpoint_invalid pid e
        (fun h=>valid (Or.inl h)) (fun h=>valid (Or.inr h)))
      g ambient result final after run)
end Leanux.Proofs.WG.Config.GetterPeerCommand
