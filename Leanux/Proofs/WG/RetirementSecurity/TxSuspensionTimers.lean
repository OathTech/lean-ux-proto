import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionNative

/-! Native timer-arm and clock paths preserve the suspended actor records.
Timer wheel changes remain ordinary WG state effects and do not serve or
discard a TX worker obligation. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem ambient_get : Keeps (getAmbient : StateT S AmbientM Ambient) := by
  apply ambient
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem peek_site : Keeps (peekHiddenSite : StateT S AmbientM (Option Nat)) :=
  ambient TxActorFrames.peek_site

theorem jiffies (site : HiddenSite) : Keeps (hiddenJiffies site : StateT S AmbientM UInt64) := by
  apply ambient
  exact (TxActorFrames.hidden site).bind (fun _=>SameView.pure _ _)

theorem clock (site : HiddenSite) : Keeps (hiddenClock64 site : StateT S AmbientM Int64) := by
  apply ambient
  exact (TxActorFrames.hidden site).bind (fun _=>SameView.pure _ _)

theorem caller_jiffies (site : HiddenSite) : Keeps (callerJiffies site) := by
  unfold callerJiffies
  repeat' first | env_operation_fact ambient_get | env_operation_fact jiffies | suspension_step

theorem place (pid : PeerId) (timer : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
    Keeps (placeOnWheel pid timer expires clk unit) := by
  suspension_source [placeOnWheel] using [peer,set_peer,peek_site,hidden,invariant]

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64) :
    Keeps (armTimer pid timer delay jc) := by
  suspension_source [armTimer] using [place,ambient_get,peer,device,hidden,invariant,unsupported]

theorem delete (pid : PeerId) (timer : PeerTimer) : Keeps (delTimer pid timer) := by
  unfold delTimer
  repeat' first | env_operation_fact peer | env_operation_fact set_peer | suspension_step

theorem guard (pid : PeerId) : Keeps (modPeerTimerGuard pid) := by
  unfold modPeerTimerGuard WG.andM
  repeat' first | env_operation_fact peer | env_operation_fact device | env_operation_fact branch | suspension_step

theorem timer (site : HiddenSite) (pid : PeerId) (kind : PeerTimer) (delay : Nat) :
    Keeps (modPeerTimer site pid kind delay) := by
  unfold modPeerTimer
  repeat' first | env_operation_fact caller_jiffies | env_operation_fact guard | env_operation_fact arm | suspension_step

theorem traversal (pid : PeerId) : Keeps (timersTraversal pid) := by
  unfold timersTraversal
  repeat' first | env_operation_fact peer | env_operation_fact compare | env_operation_fact timer | suspension_step

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
