import Leanux.Proofs.WG.TimerDiscipline.View
import Leanux.Proofs.WG.TimerDiscipline.JitterFrames
import Leanux.Proofs.WG.TimerDiscipline.SendBufferFrame
import Leanux.Proofs.WG.TimerDiscipline.ArmingLifecycleClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem traversal_initiationView (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ timersTraversal pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases hd : g.dev with
  | none => simp [initiationAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [initiationAt, peerAt, hd, hp] at pre
    | some p =>
      have hv : initiationView p = v := by simpa [initiationAt, peerAt, hd, hp] using pre
      have effect := timersTraversal_effect pid d p hp (Campaign2.snapshot g ambient)
        g ambient result final after ⟨rfl, hd⟩ run
      change (((Campaign2.snapshot final after).wg.device.bind fun d => d.peers[pid]?).map initiationView) = some v
      split at effect
      · cases mode : ambient.armRecords with
        | false =>
          simp only [peerTimerArmEffect, Campaign2.snapshot, mode, Bool.false_eq_true, ite_false] at effect
          refine (congrArg (fun state : Campaign2.State =>
                (state.device.bind fun dev => dev.peers[pid]?).map initiationView) effect).trans ?_
          cases placed : TimerWheel.place p .persistentKeepalive
            (g.jiffiesLast.getD 0 + (p.persistentKeepaliveInterval * HZ).toUInt64) (g.jiffiesLast.getD 0) <;>
            simp only [wheelPlacementView, placed]
          all_goals simp [Campaign2.core, hd, initiationView, Peer.setTimer, Peer.setWheel, ← hv]
        | true =>
          simp only [peerTimerArmEffect, Campaign2.snapshot, mode, ite_true] at effect
          obtain ⟨caller, now, unit, _, _, effect⟩ := effect
          split at effect
          · refine (congrArg (fun state : Campaign2.State =>
                (state.device.bind fun dev => dev.peers[pid]?).map initiationView) effect).trans ?_
            simpa [recordedArmPrefixView, Campaign2.core, hd, hp] using congrArg some hv
          · obtain ⟨clk, effect⟩ := effect
            refine (congrArg (fun state : Campaign2.State =>
                (state.device.bind fun dev => dev.peers[pid]?).map initiationView) effect).trans ?_
            cases placed : TimerWheel.place p .persistentKeepalive
              (caller + (p.persistentKeepaliveInterval * HZ).toUInt64) clk <;>
              simp only [wheelPlacementView, placed]
            all_goals simp [recordedArmPrefixView, Campaign2.core, hd,
              initiationView, Peer.setTimer, Peer.setWheel, ← hv]
      · refine (congrArg (fun state : Campaign2.State =>
                (state.device.bind fun dev => dev.peers[pid]?).map initiationView) effect).trans ?_
        simpa [Campaign2.snapshot, Campaign2.core, hd, hp] using congrArg some hv

theorem delKeepalive_initiationView (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ timersAnyAuthenticatedPacketSent pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold timersAnyAuthenticatedPacketSent delTimer
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid (fun g => initiationAt g pid = some v))) ?_
  intro p g ambient result final after pre run
  have value : initiationView p = v := by simpa [initiationAt, pre.2] using pre.1
  exact (ensures_iff _ _ _).mpr (setPeer_initiationView pid v _)
    g ambient result final after ⟨by simpa [initiationView, Peer.setTimer, Peer.setWheel] using value, pre.1⟩ run

theorem initiationArmPrefix_view (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ initiationArmPrefix pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  let P : WGWorld → Prop := fun g => initiationAt g pid = some v
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) := hambient (AmbientM.branch site value)
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient result final after pre run).1
  have hclock (birthday : Int64) :
      Ensures (branchExpired .initRateLimited birthday REKEY_TIMEOUT (!·)) P (fun _ => P) := by
    simp only [branchExpired, birthdateTest, bind_assoc, pure_bind]
    refine ensures_bind (Q := fun _ => P) _ _ (hambient (AmbientM.hiddenClock64 .birthdateExpired)) ?_
    intro now
    exact hambient (AmbientM.branchCmp _ _ _ _)
  have hstop (message : String) : Ensures (invariant message : WG.M Bool) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run
  have hwrite (now : Int64) : Ensures (do
      let p ← getPeer pid
      setPeer pid {p with lastSentHandshake := now}) P (fun _ => P) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro p g ambient result final after pre run
    have value : initiationView p = v := by simpa [P, initiationAt, pre.2] using pre.1
    exact (ensures_iff _ _ _).mpr (setPeer_initiationView pid v {p with lastSentHandshake := now})
      g ambient result final after ⟨value, pre.1⟩ run
  have writeBind {α : Type} (now : Int64) (next : WG.M α) (rest : Ensures next P (fun _ => P)) :
      Ensures (do
        let p ← getPeer pid
        setPeer pid {p with lastSentHandshake := now}
        next) P (fun _ => P) := by
    simpa only [bind_assoc] using ensures_bind _ (fun _ => next) (hwrite now) (fun _ => rest)
  have hmac (msg : List UInt8) : Ensures (addMacToPacket pid msg) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (addMacToPacket_view pid msg v)
  have hsend (msg : List UInt8) : Ensures (sendBufferToPeer pid msg) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (sendBufferToPeer_spec_initiation_variant pid msg v)
  have htraversal := (ensures_iff _ _ _).mpr (traversal_initiationView pid v)
  have hdel := (ensures_iff _ _ _).mpr (delKeepalive_initiationView pid v)
  have hcreate := (ensures_iff _ _ _).mpr (createInitiation_view pid v)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (yesFrame : Ensures yes P (fun _ => P)) (noFrame : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by split <;> assumption
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  unfold initiationArmPrefix
  refine ensures_bind _ _ hread ?_
  intro peer
  refine ensures_bind _ _ (hclock peer.lastSentHandshake) ?_
  intro limited
  cases limited with
  | true => exact hpure false
  | false =>
    refine ensures_bind _ _ (hambient (AmbientM.hiddenClock64 .initLastSent)) ?_
    intro now
    refine writeBind now _ ?_
    refine ensures_bind _ _ hcreate ?_
    intro created
    cases created
    all_goals
      repeat' first
        | exact hpure _
        | exact hambient _
        | exact hbranch _ _
        | exact hread
        | exact hstop _
        | exact hwrite _
        | exact hmac _
        | exact hsend _
        | exact htraversal
        | exact hdel
        | (apply writeBind)
        | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
        | (refine hif _ _ _ ?_ ?_)

def workerAt (w : WGWorld) (pid : PeerId) : Option WorkerView := (peerAt w pid).map workerView

theorem timersHandshakeInitiated_workerView (pid : PeerId) (v : WorkerView) :
    ⦃fun w => ⌜workerAt w pid = some v⌝⦄ timersHandshakeInitiated pid
      ⦃⇓? _ w => ⌜workerAt w pid = some v⌝⦄ := by
  let P : WGWorld → Prop := fun g => workerAt g pid = some v
  have hpure : Ensures (pure () : WG.M Unit) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hcaller : Ensures (callerJiffies .timerJiffiesHandshakeInitiated) P (fun _ => P) := by
    intro g ambient result final after pre run
    rw [(callerJiffies_input_effect _ g final ambient after result run).1]
    exact pre
  have hguard : Ensures (modPeerTimerGuard pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [P, workerAt, peerAt, device] at pre
    | some d =>
      cases found : d.peers[pid]? with
      | none => simp [P, workerAt, peerAt, device, found] at pre
      | some p =>
        rw [(modPeerTimerGuard_input_effect pid d p found g final ambient after result device run).2.1]
        exact pre
  have harm (delay : Nat) (caller : Option UInt64) :
      Ensures (armTimer pid .retransmitHandshake delay caller) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases result
    cases device : g.dev with
    | none => simp [P, workerAt, peerAt, device] at pre
    | some d =>
      cases found : d.peers[pid]? with
      | none => simp [P, workerAt, peerAt, device, found] at pre
      | some p =>
        have resident : peerAt g pid = some p := by simp [peerAt, device, found]
        have value : workerView p = v := by simpa [P, workerAt, resident] using pre
        have wheelFrame (entry : WGWorld) (same : entry.dev = some d) (expires clk : UInt64) :
            P (wheelPlacementState entry pid p .retransmitHandshake expires clk) := by
          cases placed : TimerWheel.place p .retransmitHandshake expires clk <;>
            simpa [P, workerAt, peerAt, wheelPlacementState, placed, same,
              workerView, Peer.setTimer, Peer.setWheel] using value
        cases mode : ambient.armRecords with
        | false =>
          rw [armTimer_off_effect pid .retransmitHandshake delay caller g p resident ambient after final mode run]
          exact wheelFrame g device _ _
        | true =>
          cases caller with
          | none =>
            have ambientRead : ((getAmbient : WG.M Ambient).run g).run ambient = .ok ((ambient, g), ambient) := rfl
            have hiddenRead : ((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient =
                ((AmbientM.hidden .modTimerArm).run ambient >>= fun (bytes, next) => .ok ((bytes, g), next)) := rfl
            simp only [armTimer, StateT.run_bind, StateT.run_get, pure_bind] at run
            rw [ambientRead] at run
            simp only [bind, Except.bind, mode, Bool.not_true, Bool.false_eq_true, ite_false] at run
            change (((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient >>= _) = _ at run
            rw [hiddenRead] at run
            cases read : (AmbientM.hidden .modTimerArm).run ambient with
            | error err => rw [read] at run; cases run
            | ok out => rw [read] at run; cases out; cases run
          | some caller =>
            by_cases same : p.timer .retransmitHandshake = some (caller + delay.toUInt64)
            · obtain ⟨now, unit, _, _, effect⟩ := armTimer_sameExpiry_effect pid .retransmitHandshake delay caller
                g p resident same ambient after final mode run
              rw [effect]
              exact pre
            · obtain ⟨now, unit, clk, _, _, effect⟩ := armTimer_changedExpiry_effect pid .retransmitHandshake delay caller
                g p resident same ambient after final mode run
              rw [effect]
              exact wheelFrame {recordedArmPrefixState g pid .retransmitHandshake now unit with timerClk := some clk} device _ _
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  unfold timersHandshakeInitiated
  refine ensures_bind _ _ hcaller ?_
  intro caller
  refine ensures_bind _ _ (jitter_wg_spec P .retransmitJitter) ?_
  intro jitter
  refine ensures_bind _ _ hguard ?_
  intro allowed
  cases allowed with
  | false => exact hpure
  | true => exact harm (REKEY_TIMEOUT_TICKS + jitter) caller

end Leanux.Proofs.WG.TimerDiscipline
