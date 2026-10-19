import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveFrames
import Leanux.Proofs.WG.RetirementSecurity.TxDestructSource

/-! Native frames at the destructor's final checked suffix. The reset has an
empty projection but does not claim that any old obligation was discharged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity

theorem settle : SameView StagedEntry.view TxWork.Destruct.settle := by
  unfold TxWork.Destruct.settle
  apply SameView.bind (TimerFrames.store mayHaveSlept_sameWGStore)
  intro _
  apply SameView.bind (ReceiveFrames.device (fun d => {d with handshakeQueueLen := 0}) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  intro _
  apply SameView.bind (TimerFrames.store mayHaveSlept_sameWGStore)
  intro _
  exact ratelimiterUninit_sameRatelimiter.of_factor
    (fun s => StagedEntry.view {dev := s.dev}) _ (fun _ => rfl)

theorem absent_staged (absent : w.dev = none) (epoch : Nat) (pid : PeerId) (stamp : Nat) :
    stagedPackets epoch pid stamp w = [] := by
  simp [stagedPackets,Packets.epoch,absent]

theorem absent_cells (absent : w.dev = none) :
    TxDisposition.txPackets w = fun _ => none := by
  funext id
  simp [TxDisposition.txPackets,absent]

theorem absent_bounds (absent : w.dev = none) : Packets.Inv w := by
  simp [Packets.Inv,Packets.snapshot,absent,Bounded]

theorem absent_coverage (absent : w.dev = none) : TxCoverage [] w := by
  intro id packet found
  simp [TxDisposition.txPackets,absent] at found

theorem absent_inventory (absent : w.dev = none) : TxInventory [] w := by
  constructor
  · simp [txLocalItems]
  · intro pid p found
    simp [peerAt,absent] at found
  · intro pid p other q found
    simp [peerAt,absent] at found
  · intro pid p found
    simp [peerAt,absent] at found
  · intro id member
    simp [txLocalItems] at member
  · intro pid p found
    simp [peerAt,absent] at found

/-- This is the literal reset suffix, after the destructor's checked prefix. -/
def reset : WG.M Unit := do
  _root_.modify fun w : WGWorld => {w with dev := none}
  retireDeviceUnits

theorem reset_absent (run : (reset.run w).run a = .ok (((),v),b)) : v.dev = none := by
  unfold reset at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨value,u,c,erased,retired⟩ := run
  cases erased
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    retireDeviceUnits_sameWGStore _ _ () v b retired
  exact congrArg WGStoreView.dev same

theorem destructor_factor : wgDestruct = (do TxWork.Destruct.beforeReset; reset) :=
  TxWork.Destruct.factor

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredFrames
