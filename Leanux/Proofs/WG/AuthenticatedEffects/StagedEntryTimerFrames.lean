import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueuedCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedPeerViewFrames
import Leanux.Proofs.WG.RetirementSecurity.TxCryptTimerFrames
import Leanux.Proofs.WG.RetirementSecurity.OwnershipSourceFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionTimerGeometry

/-! Exact native timer frames for the complete entry carrier. These retain
the packet allocation frontier and RX store as well as TX cells and owners;
an encryption-ring frame alone would not establish the packet bounds. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TimerFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
open RetirementSecurity.StagingOccurrences Queues.RxCredits
set_option maxHeartbeats 600000

theorem combine {action : WG.M α}
    (epoch : SameView Packets.epoch action) (staged : SameView Staged.stagedAt action)
    (geometry : SameView StagingOccurrences.geometry action)
    (queues : SameView txQueueContents action) : SameView StagedEntry.view action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  have e := (ProjectedAction.iff_run_ambient _ _ _).mp epoch w a value v b run
  have s := (ProjectedAction.iff_run_ambient _ _ _).mp staged w a value v b run
  have g := (ProjectedAction.iff_run_ambient _ _ _).mp geometry w a value v b run
  have q := (ProjectedAction.iff_run_ambient _ _ _).mp queues w a value v b run
  have snapshot : Packets.snapshot v = Packets.snapshot w := congrArg Prod.fst g
  have packets : TxDisposition.txPackets v = TxDisposition.txPackets w := congrArg Prod.snd g
  have material : PacketMaterial.view v = PacketMaterial.view w := by
    funext id
    simp only [PacketMaterial.view,packets]
  exact congrArg (fun x => x) (show StagedEntry.view v = StagedEntry.view w from
    Prod.ext e (Prod.ext s (Prod.ext material (Prod.ext snapshot (Prod.ext packets q)))))

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64) :
    SameView StagedEntry.view (armTimer pid timer delay clock) :=
  combine (PacketOrigins.epoch_ring ((armTimer_cryptWire pid timer delay clock).factor Prod.fst))
    (Staged.Exact.arm pid timer delay clock) (AllocatedObligation.CompletionGeometry.armTimer_geometry pid timer delay clock)
    (contents_factor (ownership_queues (armTimer_ownership pid timer delay clock)))

theorem delete (pid : PeerId) (timer : PeerTimer) : SameView StagedEntry.view (delTimer pid timer) :=
  Queued.update pid (fun p => (p.setTimer timer none).setWheel timer none)
    (fun _ => by cases timer <;> exact ⟨rfl,rfl,rfl⟩)

theorem store {action : WG.M α} (same : SameWGStore action) : SameView StagedEntry.view action :=
  same.of_factor (fun s => StagedEntry.view {dev := s.dev}) StagedEntry.view (fun _ => rfl)

theorem branch_frame (decision : Decision) (value : Bool) :
    SameView StagedEntry.view (branch decision value : WG.M Bool) :=
  fun initial => hoare_liftAmbient (AmbientM.branch decision value) (fun w => StagedEntry.view w = initial)

theorem hidden_frame (site : HiddenSite) : SameView StagedEntry.view (hidden site : WG.M (List UInt8)) :=
  fun initial => hoare_liftAmbient (AmbientM.hidden site) (fun w => StagedEntry.view w = initial)

macro "entry_timer_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact (store getDev_sameWGStore).wp (· = $initial))
  | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w => StagedEntry.view w = $initial))
  | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => StagedEntry.view w = $initial))
  | (rx_retention_head hidden; unfold hidden; exact hoare_liftAmbient _ _)
  | queued_entry_step $initial)

theorem guard (pid : PeerId) : SameView StagedEntry.view (modPeerTimerGuard pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold modPeerTimerGuard WG.andM
  simp only [branch]
  repeat' entry_timer_step initial

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView StagedEntry.view (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  apply SameView.bind ((callerJiffies_sameWGWorld site).factor StagedEntry.view)
  intro clock
  apply SameView.bind (guard pid)
  intro ready
  split
  · exact (arm pid timer delay clock).bind (fun _ => SameView.pure _ _)
  · exact SameView.pure _ _

macro "entry_timer_native_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head modPeerTimer; exact (modify_timer _ _ _ _).wp (· = $initial))
  | (rx_retention_head armTimer; exact (arm _ _ _ _).wp (· = $initial))
  | (rx_retention_head delTimer; exact (delete _ _).wp (· = $initial))
  | (rx_retention_head modPeerTimerGuard; exact (guard _).wp (· = $initial))
  | entry_timer_step $initial)

theorem received (pid : PeerId) : SameView StagedEntry.view (timersDataReceived pid) := by
  unfold timersDataReceived
  apply SameView.bind (store getDev_sameWGStore)
  intro d
  apply SameView.bind (branch_frame _ _)
  intro running
  split
  · apply SameView.bind (Queued.read pid)
    intro p
    apply SameView.bind (branch_frame _ _)
    intro ready
    split
    · exact (modify_timer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).map (fun _ => ())
    · exact Queued.update pid (fun p => {p with timerNeedAnotherKeepalive := true}) (fun _ => ⟨rfl,rfl,rfl⟩)
  · exact SameView.pure _ _

theorem sent (pid : PeerId) : SameView StagedEntry.view (timersDataSent pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold timersDataSent
  simp only [branch]
  repeat' entry_timer_native_step initial

theorem traversal (pid : PeerId) : SameView StagedEntry.view (timersTraversal pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold timersTraversal
  simp only [branchCmp,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' entry_timer_native_step initial

theorem derived (pid : PeerId) : SameView StagedEntry.view (timersSessionDerived pid) :=
  (modify_timer .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).map (fun _ => ())

theorem initiated (pid : PeerId) : SameView StagedEntry.view (timersHandshakeInitiated pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold timersHandshakeInitiated
  repeat' entry_timer_native_step initial

theorem handshake_complete (pid : PeerId) (site : HiddenSite) :
    SameView StagedEntry.view (timersHandshakeComplete pid site) := by
  have reset := Queued.update pid
    (fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false})
    (fun _ => ⟨rfl,rfl,rfl⟩)
  have wall (now : List UInt8) := Queued.update pid
    (fun p => {p with walltimeLastHandshake := now}) (fun _ => ⟨rfl,rfl,rfl⟩)
  have grouped : timersHandshakeComplete pid site = (do
      delTimer pid .retransmitHandshake
      (getPeer pid >>= fun p => setPeer pid {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false})
      let now ← hidden site
      (getPeer pid >>= fun p => setPeer pid {p with walltimeLastHandshake := now})) := by
    simp only [timersHandshakeComplete,bind_assoc]
  rw [grouped]
  apply SameView.bind (delete pid .retransmitHandshake)
  intro ignored
  apply SameView.bind reset
  intro ignored
  apply SameView.bind (hidden_frame site)
  exact wall

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TimerFrames
