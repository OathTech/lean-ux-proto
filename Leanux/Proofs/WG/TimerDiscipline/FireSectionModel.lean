import Leanux.Proofs.WG.TimerDiscipline.RetryReadySource
import Leanux.Proofs.WG.TimerDiscipline.WheelDispatchSource

/-! Explicit section and callback records, detached timer state, and the exact projected effect of a ready retransmit timer. The supplied suffix remains arbitrary. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.FireReady
open Leanux Leanux.WG Leanux.Proofs.WG.TimerDiscipline

def sectionSite (start : Bool) : HiddenSite :=
  if start then .sectionStart .timerRetransmit else .sectionStop .timerRetransmit
def sectionRecord (start : Bool) (bytes : List UInt8) : HiddenRecord :=
  ⟨(sectionSite start).info.id, bytes⟩
theorem section_passive (start : Bool) (bytes : List UInt8) :
    HiddenSite.passive (sectionRecord start bytes).site = false := by
  cases start <;> rfl
theorem section_drop (start : Bool) (bytes : List UInt8) (rest : List HiddenRecord) :
    (sectionRecord start bytes :: rest).dropWhile (fun r => HiddenSite.passive r.site) =
      sectionRecord start bytes :: rest := by
  simp only [List.dropWhile_cons, section_passive, Bool.false_eq_true, ite_false]

def detachedPeer (p : Peer) : Peer :=
  (p.setTimer .retransmitHandshake none).setWheel .retransmitHandshake none
def detachedDevice (d : Device) (p : Peer) (pid : PeerId) : Device :=
  {d with peers := d.peers.insert pid (detachedPeer p)}
def afterDetach (w : World) (d : Device) (p : Peer) (pid : PeerId) : World :=
  {w with wg := {w.wg with dev := some (detachedDevice d p pid)}}
def sectionEntry (w : World) (rest : List HiddenRecord) : World :=
  {w with ambient := {w.ambient with
    fired := w.ambient.fired.push Worker.timerRetransmit.symbol
    hidden := some rest
    pendingWork := w.ambient.pendingWork.filter (· != Worker.timerRetransmit.index)}}
end Leanux.Proofs.WG.TimerDiscipline.FireReady
