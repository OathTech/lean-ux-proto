import Leanux.Proofs.WG.TimerDiscipline.FireReadyModel
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Concrete state updates and their projection. Section entry appends the fired symbol and removes the timer worker index from pending work. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.FireReady
open Leanux Leanux.WG Leanux.Proofs.WG.TimerDiscipline

def afterDetach (w : World) (d : Device) (p : Peer) (pid : PeerId) : World :=
  {w with k := {w.k with wg := some {d with peers := d.peers.insert pid (p.setTimer .retransmitHandshake none)}}}
def sectionEntry (w : World) (rest : List HiddenRecord) : World :=
  {w with
    fired := w.fired.push Worker.timerRetransmit.symbol
    hidden := some rest
    pendingWork := w.pendingWork.filter (· != Worker.timerRetransmit.index)}
def fireResult (w : World) (d : Device) (p : Peer) (pid : PeerId)
    (cache clock : List UInt8) (suffix : List HiddenRecord) : World :=
  {w with
    k := {w.k with wg := some (RetryReady.result (detachedDevice d p pid) pid
      (p.setTimer .retransmitHandshake none) cache)}
    hidden := some suffix
    steps := RetryReady.decisions (p.setTimer .retransmitHandshake none) clock w.netRxSection w.steps
    queuedThisCall := pid :: w.queuedThisCall
    fired := w.fired.push Worker.timerRetransmit.symbol
    pendingWork := w.pendingWork.filter (· != Worker.timerRetransmit.index)}
theorem fire_result_snapshot (w : World) (d : Device) (p : Peer) (pid : PeerId)
    (cache clock : List UInt8) (suffix : List HiddenRecord) :
    Campaign2.snapshot (fireResult w d p pid cache clock suffix) =
      fireView (Campaign2.snapshot w) d p pid cache clock suffix := rfl

end Leanux.Proofs.WG.TimerDiscipline.FireReady
