import Leanux.Proofs.WG.Noise.DriverTagSilentFrames
import Leanux.Proofs.WG.Noise.SendSkbRulesSource
import Leanux.Proofs.WG.Noise.InitiationArmRulesSource
import Leanux.Proofs.WG.Roaming.RemoteTransportFrames
import Leanux.Proofs.WG.Roaming.RemoteTimerFrames
import Leanux.Proofs.WG.Roaming.RemoteCreatorFrames
import Leanux.Proofs.WG.Roaming.RemoteMutationFrames
import Leanux.Proofs.WG.Roaming.RemoteSessionFrames
import Leanux.Proofs.WG.Noise.ClearWorkerClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteSilent
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing Std.Do TimerDiscipline

def Retained (entry : RemoteMap) (g : WGWorld) : Prop :=
  RemoteRetained entry (destinationAt g)

theorem of_frame {α : Type} (entry : RemoteMap) (action : WG.M α)
    (frame : SameView destinationAt action) :
    Ensures action (Retained entry) (fun _ => Retained entry) := by
  intro g a value out b pre run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame g a value out b run
  simpa only [Retained, same] using pre

theorem peerGet_retained (entry : RemoteMap) (pid : PeerId) :
    Ensures (peerGet pid) (Retained entry) (fun _ => Retained entry) :=
  staging_remotes _ (Index.StagingRich.peerGet_rich pid) entry

theorem purge_frame (pid : PeerId) : SameView destinationAt (purgeStagedPackets pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final after run
  cases device : g.dev with
  | none =>
    simp [purgeStagedPackets,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [purgeStagedPackets,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      simp [purgeStagedPackets,getPeer,getDev,device,resident,setPeer,modifyDev] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      funext target
      by_cases same : pid = target
      · subst target
        simp [destinationAt,peerAt,device,resident]
      · simp [destinationAt,peerAt,device,Std.TreeMap.getElem?_insert,same]

theorem clearRun_endpoints {pid : PeerId} {d final : Device} {slots : List ClearSlot}
    (steps : ClearRun pid d slots final) :
    responseEndpointMap (some final) = responseEndpointMap (some d) := by
  induction steps with
  | nil => rfl
  | cons d slot p middle final rest resident put tail ih =>
    refine ih.trans ?_
    have unchanged : responseEndpointMap (some middle) =
        responseEndpointMap (some (clearWrite d pid slot p)) := by
      funext target
      simp only [responseEndpointMap,Option.bind_some,clearPut_peers put]
    rw [unchanged]
    exact (pinned_const _private.Leanux.Proofs.WG.Roaming.ResponseRejectionFrames.«0».Leanux.Proofs.WG.Roaming.endpoint_write)
      d pid p (slot.clear p) resident (by cases slot <;> rfl)

theorem keypairsClear_frame (pid : PeerId) : SameView destinationAt (keypairsClear pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final after run
  cases device : g.dev with
  | none =>
    simp [keypairsClear,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [keypairsClear,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨out,found,steps⟩ := keypairsClear_effect pid d p resident g a result final after device run
      apply endpointMap_destinations
      rw [found,device]
      exact clearRun_endpoints steps

theorem handshakeClear_frame (pid : PeerId) : SameView destinationAt (handshakeClear pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final after run
  cases device : g.dev with
  | none =>
    simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have exactClear : Ensures (handshakeClear pid) (fun w => w.dev = some d)
          (fun _ w => w.dev = some (Config.expiryZeroDevice d pid p)) := by
        simpa only [Config.expiryReadPrefix,requireNotPending,pure_bind] using
          Config.expiryReadPrefix_exact pid d p resident
      have ending := exactClear g a result final after device run
      funext target
      by_cases same : pid = target
      · subst target
        simp [destinationAt,peerAt,ending,device,resident,Config.expiryZeroDevice,
          Config.withPeer,Config.zeroedHandshake]
      · simp [destinationAt,peerAt,ending,device,Config.expiryZeroDevice,
          Config.withPeer,Std.TreeMap.getElem?_insert,same]

theorem wheelPlacementState_endpoints (entry : WGWorld) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (expires clk : UInt64) (ambient : Ambient)
    (resident : peerAt entry pid = some p) :
    responseEndpointMap (wheelPlacementState entry pid p timer expires clk).dev =
      responseEndpointMap entry.dev := by
  cases device : entry.dev with
  | none => simp [peerAt,device] at resident
  | some d =>
    have found : d.peers[pid]? = some p := by simpa [peerAt,device] using resident
    have projection :
        (wheelPlacementState entry pid p timer expires clk).dev =
        (wheelPlacementView (Campaign2.snapshot entry ambient).wg pid p timer expires clk).device := by
      cases placed : TimerWheel.place p timer expires clk <;>
        simp only [wheelPlacementState,wheelPlacementView,placed] <;> rfl
    rw [projection]
    simpa only [Campaign2.snapshot,Campaign2.core,device] using
      wheelPlacementView_endpoints (Campaign2.snapshot entry ambient).wg d pid p timer expires clk device found

theorem guardedArm_frame (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (caller : Option UInt64) :
    SameView destinationAt (do if ← modPeerTimerGuard pid then armTimer pid timer delay caller) :=
by
  apply endpoint_frame_remotes
  intro entry g ambient result final after pre run
  exact InitiationCaller.guardedArm_deviceView responseEndpointMap pid timer
    (fun g p expires clk resident =>
      wheelPlacementState_endpoints g pid p timer expires clk ambient resident)
    delay caller entry g ambient result final after pre run

theorem initiated_frame (pid : PeerId) : SameView destinationAt (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated
  exact ((callerJiffies_sameWGWorld .timerJiffiesHandshakeInitiated).factor destinationAt).bind
    (fun caller => ((jitterBelowRekeyTimeout_sameWGWorld .retransmitJitter).factor destinationAt).bind
      (fun jitter => guardedArm_frame pid .retransmitHandshake (REKEY_TIMEOUT_TICKS+jitter) caller))

theorem getPeer_frame (pid : PeerId) : SameView destinationAt (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a p final after run
  exact congrArg destinationAt (Queues.getPeer_normal pid g final p a after run).1

theorem dataSent_frame (pid : PeerId) : SameView destinationAt (timersDataSent pid) := by
  rw [dataSent_source]
  unfold dataSentPrefix
  simp only [bind_assoc]
  apply (getPeer_frame pid).bind
  intro p
  apply (show SameView destinationAt (branch .timersDataSentNotPending !(p.timerPending .newHandshake)) from
    fun initial => hoare_liftAmbient (AmbientM.branch .timersDataSentNotPending !(p.timerPending .newHandshake))
      (fun g => destinationAt g=initial)).bind
  intro ready
  cases ready with
  | false => exact SameView.pure destinationAt ()
  | true =>
    unfold jitteredArm
    exact ((callerJiffies_sameWGWorld .timerJiffiesDataSent).factor destinationAt).bind (fun caller =>
      ((jitterBelowRekeyTimeout_sameWGWorld .newHandshakeJitter).factor destinationAt).bind (fun jitter =>
        guardedArm_frame pid .newHandshake (KEEPALIVE_TIMEOUT_TICKS+REKEY_TIMEOUT_TICKS+jitter) caller))

theorem sendSkb_frame (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView destinationAt (sendSkbToPeer pid bytes ds) := by
  intro initial
  exact DataCompletionRules.sendSkb_preserves _ pid bytes ds
    (fun e exactRx => remotes_frame_of_sendWork _ pid (send4_sendWorkView pid e bytes ds exactRx) initial)
    (fun e exactRx => remotes_frame_of_sendWork _ pid (send6_sendWorkView pid e bytes ds exactRx) initial)
    (modifyPeer_remotes pid (fun p => {p with txBytes:=p.txBytes+bytes.length}) (fun _ => rfl) initial)

end Leanux.Proofs.WG.Roaming.RemoteSilent
