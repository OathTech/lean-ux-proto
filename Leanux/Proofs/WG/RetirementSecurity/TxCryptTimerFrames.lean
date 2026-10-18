import Leanux.Proofs.WG.RetirementSecurity.TxCryptWireFrames

/-! Native timer completion bookkeeping preserves the encryption ring and TX packet cells. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem placeOnWheel_cryptWire (pid : PeerId) (timer : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) : SameView txCryptWire (placeOnWheel pid timer expires clk unit) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold placeOnWheel
  simp (config := {zeta := false}) only [peekHiddenSite,hidden,invariant]
  repeat' crypt_wire_step initial

theorem armTimer_cryptWire (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64 := none) : SameView txCryptWire (armTimer pid timer delay jc) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient,hidden,invariant,unsupported]
  repeat' first
    | (rx_retention_head placeOnWheel
       exact (placeOnWheel_cryptWire _ _ _ _ _).wp (fun s => s = initial))
    | crypt_wire_step initial

theorem delTimer_cryptWire (pid : PeerId) (timer : PeerTimer) :
    SameView txCryptWire (delTimer pid timer) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold delTimer
  repeat' crypt_wire_step initial

theorem modPeerTimerGuard_cryptWire (pid : PeerId) :
    SameView txCryptWire (modPeerTimerGuard pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold modPeerTimerGuard WG.andM
  simp only [branch]
  repeat' crypt_wire_step initial

theorem modPeerTimer_cryptWire (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) : SameView txCryptWire (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  apply SameView.bind ((callerJiffies_sameWGWorld site).of_factor
    txCryptWire txCryptWire (fun _ => rfl))
  intro jc
  apply SameView.bind (modPeerTimerGuard_cryptWire pid)
  intro ready
  split
  · exact (armTimer_cryptWire pid timer delay jc).bind (fun _ => SameView.pure _ _)
  · exact SameView.pure _ _

theorem timersTraversal_cryptWire (pid : PeerId) :
    SameView txCryptWire (timersTraversal pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold timersTraversal
  simp only [branchCmp]
  repeat' first
    | (rx_retention_head modPeerTimer
       exact (modPeerTimer_cryptWire _ _ _ _).wp (fun s => s = initial))
    | crypt_wire_step initial
  all_goals exact ((modPeerTimer_cryptWire _ _ _ _).map (fun _ => ())).wp (fun s => s = initial)

theorem timersDataSent_cryptWire (pid : PeerId) :
    SameView txCryptWire (timersDataSent pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold timersDataSent
  simp only [branch]
  repeat' first
    | (rx_retention_head callerJiffies
       exact (callerJiffies_sameWGWorld _).wp (fun w => txCryptWire w = initial))
    | (rx_retention_head jitterBelowRekeyTimeout
       exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => txCryptWire w = initial))
    | (rx_retention_head modPeerTimerGuard
       exact (modPeerTimerGuard_cryptWire _).wp (fun s => s = initial))
    | (rx_retention_head armTimer
       exact (armTimer_cryptWire _ _ _ _).wp (fun s => s = initial))
    | crypt_wire_step initial

end Leanux.Proofs.WG.RetirementSecurity
