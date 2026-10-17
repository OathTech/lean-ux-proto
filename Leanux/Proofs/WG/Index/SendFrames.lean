import Leanux.Proofs.WG.Index.TablePeerFrames
import Leanux.Proofs.WG.TimerDiscipline.SendBufferFrame
import Leanux.Proofs.WG.TimerDiscipline.JitterFrames
import Leanux.Proofs.WG.TimerDiscipline.ArmingChangedExpirySource
import Leanux.Proofs.WG.TimerDiscipline.TimerInputFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

private theorem callerJiffies_tables (site : HiddenSite) :
    Ensures (callerJiffies site) TablesSafeWG (fun _ => TablesSafeWG) := by
  intro g ambient result final after pre run
  have unchanged := (TimerDiscipline.callerJiffies_input_effect site g final ambient after result run).1
  rw [unchanged]
  exact pre

private theorem timerGuard_tables_resident (pid : PeerId) :
    Ensures (modPeerTimerGuard pid) TablesSafeWG
      (fun _ g => TablesSafeWG g ∧ ∃ p, peerAt g pid = some p) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [modPeerTimerGuard, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases found : d.peers[pid]? with
    | none =>
      simp [modPeerTimerGuard, getPeer, getDev, device, found, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := (TimerDiscipline.modPeerTimerGuard_exact pid d p found
        g ambient result final after device run).2
      constructor
      · intro current hd
        have same : current = d := Option.some.inj (hd.symm.trans effect)
        subst current
        exact pre d device
      · exact ⟨p, by simp [peerAt, effect, found]⟩

private theorem armTimer_tables_resident (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : Option UInt64) :
    Ensures (armTimer pid timer delay caller)
      (fun g => TablesSafeWG g ∧ ∃ p, peerAt g pid = some p) (fun _ => TablesSafeWG) := by
  have wheelCursor (g : WGWorld) (p : Peer) (expires clk : UInt64) :
      (TimerDiscipline.wheelPlacementState g pid p timer expires clk).dev.map TimerDiscipline.tableCursor =
        g.dev.map TimerDiscipline.tableCursor := by
    cases placement : TimerWheel.place p timer expires clk <;>
      cases device : g.dev <;>
      simp [TimerDiscipline.wheelPlacementState, placement, device, TimerDiscipline.tableCursor]
  intro g ambient result final after pre run
  obtain ⟨preserved, p, resident⟩ := pre
  cases result
  cases mode : ambient.armRecords with
  | false =>
    have effect := TimerDiscipline.armTimer_off_effect pid timer delay caller g p resident
      ambient after final mode run
    rw [effect]
    exact tablesSafe_of_cursor g _ (wheelCursor g p _ _) preserved
  | true =>
    cases caller with
    | none =>
      have ambientRead : ((getAmbient : WG.M Ambient).run g).run ambient =
          .ok ((ambient, g), ambient) := rfl
      have hiddenRead : ((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient =
          ((AmbientM.hidden .modTimerArm).run ambient >>= fun (bytes, next) =>
            Except.ok ((bytes, g), next)) := rfl
      simp only [armTimer, StateT.run_bind, StateT.run_get, pure_bind] at run
      rw [ambientRead] at run
      simp only [bind, Except.bind, mode, Bool.not_true, Bool.false_eq_true, ite_false] at run
      change (((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient >>= _) = _ at run
      rw [hiddenRead] at run
      cases read : (AmbientM.hidden .modTimerArm).run ambient with
      | error err => rw [read] at run; cases run
      | ok out => rw [read] at run; cases out; cases run
    | some caller =>
      by_cases same : p.timer timer = some (caller + delay.toUInt64)
      · obtain ⟨now, unit, _, _, effect⟩ :=
          TimerDiscipline.armTimer_sameExpiry_effect pid timer delay caller g p resident same
            ambient after final mode run
        rw [effect]
        exact preserved
      · obtain ⟨now, unit, clk, _, _, effect⟩ :=
          TimerDiscipline.armTimer_changedExpiry_effect pid timer delay caller g p resident same
            ambient after final mode run
        rw [effect]
        exact tablesSafe_of_cursor _ _ (wheelCursor _ p _ _) preserved

theorem sendBufferToPeer_tables (pid : PeerId) (bytes : List UInt8) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ sendBufferToPeer pid bytes
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  have h := (ensures_iff _ _ _).mpr
    (TimerDiscipline.sendBufferToPeer_spec_send_variant pid bytes
      (TimerDiscipline.sendAt g pid).1 (TimerDiscipline.sendAt g pid).2)
    g ambient result final after rfl run
  exact tablesSafe_of_cursor g final (congrArg Prod.fst h) pre

theorem modPeerTimer_tables (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ modPeerTimer site pid timer delay
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold modPeerTimer
  refine ensures_bind _ _ (callerJiffies_tables site) ?_
  intro caller
  refine ensures_bind _ _ (timerGuard_tables_resident pid) ?_
  intro allowed
  cases allowed with
  | false =>
    intro g ambient result final after pre run
    cases run
    exact pre.1
  | true =>
    refine ensures_bind _ _ (armTimer_tables_resident pid timer delay caller) ?_
    intro u g ambient result final after pre run
    cases run
    exact pre

theorem traversal_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ timersTraversal pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  unfold timersTraversal
  refine ensures_bind _ _ read ?_
  intro peer
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.branchCmp .traversalKeepalive
      (peer.persistentKeepaliveInterval != 0) peer.persistentKeepaliveInterval 0) TablesSafeWG)) ?_
  intro enabled
  cases enabled with
  | false =>
    intro g ambient result final after pre run
    cases run
    exact pre
  | true =>
    have mapped := TimerDiscipline.map_result_native_spec (fun _ : Bool => PUnit.unit)
      (modPeerTimer .timerJiffiesTraversal pid .persistentKeepalive (peer.persistentKeepaliveInterval * HZ))
      TablesSafeWG (fun _ => TablesSafeWG)
      (modPeerTimer_tables .timerJiffiesTraversal pid .persistentKeepalive (peer.persistentKeepaliveInterval * HZ))
    intro g ambient result final after pre run
    obtain ⟨_, _, preserved⟩ := (ensures_iff _ _ _).mpr mapped
      g ambient result final after pre run
    exact preserved

theorem delKeepalive_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ timersAnyAuthenticatedPacketSent pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold timersAnyAuthenticatedPacketSent delTimer
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  exact ensures_bind _ _ read (fun p => (ensures_iff _ _ _).mpr (setPeer_tables pid _))

theorem timersHandshakeInitiated_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ timersHandshakeInitiated pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold timersHandshakeInitiated
  refine ensures_bind _ _ (callerJiffies_tables .timerJiffiesHandshakeInitiated) ?_
  intro caller
  refine ensures_bind _ _ (TimerDiscipline.jitter_wg_spec TablesSafeWG .retransmitJitter) ?_
  intro jitter
  refine ensures_bind _ _ (timerGuard_tables_resident pid) ?_
  intro allowed
  cases allowed with
  | false =>
    intro g ambient result final after pre run
    cases run
    exact pre.1
  | true => exact armTimer_tables_resident pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) caller

end Leanux.Proofs.WG.Index
