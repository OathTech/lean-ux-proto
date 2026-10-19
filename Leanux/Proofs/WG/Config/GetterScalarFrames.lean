import Leanux.Proofs.WG.Config.GetterScalarEffects
import Leanux.Proofs.WG.Config.PeerScalarRetentionFrames
import Leanux.Proofs.WG.Config.ScalarAllowedFrames
import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Config.ExpiryReadSource
import Leanux.Proofs.WG.Noise.InitiationArmRulesSource
import Leanux.Proofs.WG.Noise.MacSource
import Leanux.Proofs.WG.Index.FlushSource
import Leanux.Proofs.WG.TimerDiscipline.SendBufferFrame
import Leanux.Proofs.WG.TimerDiscipline.ArmingLifecycleClaims
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
def view (g : WGWorld) : Map := values g.dev

def Retained (entry : Map) (g : WGWorld) : Prop :=
  ∀ pid c, view g pid=some c → entry pid=some c

theorem set_peer (pid : PeerId) (p q : Peer) (same : GetterScalar.cell q=GetterScalar.cell p) (entry : Map) :
    Ensures (setPeer pid q) (fun g=>view g=entry ∧ peerAt g pid=some p)
      (fun _ g=>view g=entry) := by
  intro g a result final b pre run
  cases run
  cases device:g.dev with
  | none=>simp [peerAt,device] at pre
  | some d=>
    have resident : d.peers[pid]?=some p := by simpa [peerAt,device] using pre.2
    change values (g.dev.map fun d=>{d with peers:=d.peers.insert pid q})=entry
    rw [device]
    exact (write_values d pid p q resident same).trans (by simpa only [view,device] using pre.1)

theorem modify_peer (pid : PeerId) (f : Peer → Peer) (same : ∀p,GetterScalar.cell (f p)=GetterScalar.cell p) :
    SameView view (modifyPeer pid f) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid (fun g=>view g=entry)))
    (fun p=>set_peer pid p (f p) (same p) entry)

theorem modify_device (f : Device → Device) (same : ∀d,values (some (f d))=values (some d)) :
    SameView view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  cases run
  cases device:g.dev with
  | none=>simp only [view,device,Option.map_none]
  | some d=>simpa only [view,device,Option.map_some] using same d

theorem of_frame {α : Type} (entry : Map) (action : WG.M α) (frame : SameView view action) :
    Ensures action (Retained entry) (fun _=>Retained entry) := by
  intro g a result final b pre run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame g a result final b run
  simpa only [Retained,same] using pre

theorem rich_retained {g final : WGWorld} (frame : Index.StagingRich.Frame g final) :
    Retained (view g) final := by
  have old:=PeerScalarRetention.frame_retained frame
  intro pid c found
  let project (c : PeerScalarRetention.Cell) : Cell :=
    (c.1,c.2.1,c.2.2.1,c.2.2.2.map TimerDiscipline.socketEndpoint)
  have mapped (w : WGWorld) :
      view w pid=(PeerScalarRetention.view w pid).map project := by
    simp only [view,values,PeerScalarRetention.view,PeerScalarRetention.peerValues,
      Option.map_map,Function.comp_def,PeerScalarRetention.cell,project]
    rfl
  rw [mapped] at found ⊢
  cases present:PeerScalarRetention.view final pid with
  | none=>simp [present] at found
  | some previous=>
    rw [old pid previous present]
    simpa only [present] using found

theorem peer_put (entry : Map) (peer : Option PeerId) :
    Ensures (peerPut peer) (Retained entry) (fun _=>Retained entry) := by
  intro g a result final b pre run
  have frame:=Index.StagingRich.peerPut_rich g peer g a result final b
    (Index.StagingRich.refl g) run
  intro pid c found
  exact pre pid c (rich_retained frame pid c found)

theorem socket (pid : PeerId) (bytes : List UInt8) :
    SameView view (sendBufferToPeer pid bytes) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  have same := (ensures_iff _ _ _).mpr
    (TimerDiscipline.sendBufferToPeer_spec_sendWork_variant pid bytes
      (TimerDiscipline.sendWorkAt g pid).1 (TimerDiscipline.sendWorkAt g pid).2)
    g a result final b rfl run
  let project (x : TimerDiscipline.SendWorkCell) : Cell :=
    (x.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.2.2.1,
      x.2.2.2.2.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.2.2.2.2)
  let projectView (s : TimerDiscipline.SendWorkView) : Map :=
    fun target => (s.1.bind fun d=>d.2.2.1 target).map project
  have mapped (w : WGWorld) : projectView (TimerDiscipline.sendWorkAt w pid)=view w := by
    funext target
    cases device:w.dev <;>
      simp [projectView,TimerDiscipline.sendWorkAt,TimerDiscipline.sendWorkKernel,
        TimerDiscipline.sendWorkDevice,TimerDiscipline.sendWorkCell,device,
        Option.map_map,Function.comp_def,view,values,project] <;> rfl
  have projected:=congrArg projectView same
  rw [mapped,mapped] at projected
  exact projected

theorem scalar_frame {α : Type} {action : WG.M α}
    (frame : SameView PeerScalarRetention.view action) : SameView view action := by
  apply frame.of_factor
    (fun m pid=>(m pid).map fun c=>(c.1,c.2.1,c.2.2.1,
      c.2.2.2.map TimerDiscipline.socketEndpoint)) view
  intro g
  funext pid
  simp only [view,values,PeerScalarRetention.view,PeerScalarRetention.peerValues,
    Option.map_map,Function.comp_def,PeerScalarRetention.cell]
  rfl

theorem keypairs_clear (pid : PeerId) : SameView view (keypairsClear pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  cases device:g.dev with
  | none=>simp [keypairsClear,getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d=>
    cases resident:d.peers[pid]? with
    | none=>simp [keypairsClear,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p=>
      obtain ⟨out,found,steps⟩:=keypairsClear_effect pid d p resident g a result final b device run
      exact (show view final=values (some out) from congrArg values found).trans
        ((clearRun_values steps).trans (congrArg values device.symm))

theorem handshake_clear (pid : PeerId) : SameView view (handshakeClear pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  cases device:g.dev with
  | none=>simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run; cases run
  | some d=>
    cases resident:d.peers[pid]? with
    | none=>simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p=>
      have exactClear : Ensures (handshakeClear pid) (fun w=>w.dev=some d)
          (fun _ w=>w.dev=some (expiryZeroDevice d pid p)) := by
        simpa only [expiryReadPrefix,requireNotPending,pure_bind] using
          expiryReadPrefix_exact pid d p resident
      have ending:=exactClear g a result final b device run
      unfold view
      rw [ending,device]
      exact write_values d pid p (zeroedHandshake p) resident rfl

theorem traversal (pid : PeerId) : SameView view (timersTraversal pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  cases device:g.dev with
  | none=>simp [timersTraversal,getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d=>
    cases resident:d.peers[pid]? with
    | none=>simp [timersTraversal,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p=>
      have effect:=timersTraversal_effect pid d p resident (Campaign2.snapshot g a)
        g a result final b ⟨rfl,device⟩ run
      split at effect
      · exact arm_values (Campaign2.snapshot g a) d pid p .persistentKeepalive
          (p.persistentKeepaliveInterval*HZ) (Campaign2.snapshot final b).wg device resident effect
      · exact congrArg (fun s:Campaign2.State=>values s.device) effect

theorem delete_timer (pid : PeerId) (timer : PeerTimer) : SameView view (delTimer pid timer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  cases device:g.dev with
  | none=>simp [delTimer,getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d=>
    cases resident:d.peers[pid]? with
    | none=>simp [delTimer,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
    | some p=>
      have effect:=delTimer_exact pid timer p (Campaign2.snapshot g a)
        g a result final b ⟨rfl,by change peerAt g pid=some p;simp [peerAt,device,resident]⟩ run
      have projected:=congrArg (fun s:Campaign2.Snapshot=>values s.wg.device) effect
      change view final=_ at projected
      rw [projected]
      change values (g.dev.map fun d=>{d with peers:=d.peers.insert pid ((p.setTimer timer none).setWheel timer none)})=values g.dev
      rw [device]
      exact write_values d pid p _ resident (by cases timer <;> rfl)

theorem wheel_native (g : WGWorld) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (expires clk : UInt64)
    (resident : peerAt g pid=some p) :
    values (wheelPlacementState g pid p timer expires clk).dev=values g.dev := by
  cases device:g.dev with
  | none=>simp [peerAt,device] at resident
  | some d=>
    have found:d.peers[pid]?=some p := by simpa [peerAt,device] using resident
    unfold wheelPlacementState
    split
    all_goals
      simp only [device,Option.map_some]
      exact write_values d pid p _ found (by cases timer <;> rfl)

theorem guarded_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    SameView view (do if ←modPeerTimerGuard pid then armTimer pid timer delay caller) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  exact InitiationCaller.guardedArm_deviceView values pid timer
    (fun g p expires clk resident=>wheel_native g pid p timer expires clk resident)
    delay caller g.dev g a result final b rfl run

theorem initiated (pid : PeerId) : SameView view (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated
  exact ((callerJiffies_sameWGWorld .timerJiffiesHandshakeInitiated).factor view).bind
    (fun caller=>((jitterBelowRekeyTimeout_sameWGWorld .retransmitJitter).factor view).bind
      (fun jitter=>guarded_arm pid .retransmitHandshake (REKEY_TIMEOUT_TICKS+jitter) caller))

theorem mac (pid : PeerId) (msg : List UInt8) : SameView view (addMacToPacket pid msg) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  apply addMacToPacket_preserves pid msg (fun g=>view g=entry)
  intro p
  exact set_peer pid p {p with
    lastMac1Sent:=blake2s 16 p.cookieMac1Key (msg.take (msg.length-32)),
    haveSentMac1:=true} rfl entry

theorem index_frame {α : Type} (action : IndexM α) : SameView view (liftIndex action) := by
  intro entry
  apply hoare_liftIndex
  intro g d store pre device
  change values (some d)=entry
  simpa only [view,device] using pre

theorem prepare (pid : PeerId) : SameView view (Index.flushedSendPrepare pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  cases device:g.dev with
  | none=>
    simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d=>
    cases resident:d.peers[pid]? with
    | none=>
      simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p=>
      cases pending:p.handshakePending with
      | false=>
        simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,resident,pending,invariant,AmbientM.invariant] at run
        cases run
      | true=>
        simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,resident,pending,setPeer] at run
        obtain ⟨⟨rfl,rfl⟩,rfl⟩:=run
        change values (some {d with peers:=d.peers.insert pid {p with handshakePending:=decide (pid ∈ d.sendWorkQueue.erase pid)}})=values g.dev
        rw [device]
        exact write_values d pid p {p with handshakePending:=decide (pid ∈ d.sendWorkQueue.erase pid)} resident rfl

theorem read_device : SameView view getDev := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  obtain ⟨rfl,rfl,_⟩:=Queues.RxCredits.DecryptCarrier.getDev_current a b run
  rfl

theorem free_frame : SameView view WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  have effect:=(hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.free_storeView (wgStoreView g)) g a result final b rfl run
  have peers:=congrArg (fun s:WGStoreView×(PeerId→Option Peer)=>
    fun pid=>(s.2 pid).map GetterScalar.cell) effect
  funext pid
  unfold view values
  unfold GetterScalar.cell
  simpa [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,
    wgStoreView,Option.map_bind,Option.map_map,Option.bind_map,Function.comp_def,
    AllowedIps.resetAllowedips,GetterScalar.cell] using congrFun peers pid

end Leanux.Proofs.WG.Config.GetterScalar
