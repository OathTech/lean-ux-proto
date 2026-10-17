import Leanux.Proofs.WG.TimerDiscipline.FireReadyModel

/-! Actual Product intermediate states and their exact projection for a selected wheel unit. These are source-state helpers, not excluded-state frame facts. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.FireReady
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.TimerDiscipline
def dispatchEntry (w : World) (d : Device) (p : Peer) (pid : PeerId)
    (we : WheelEntry) : World :=
  {afterDetach w d p pid with wg := {(afterDetach w d p pid).wg with timerPassStep := some we.bucketExpiry}}

def fireResult (w : World) (d : Device) (p : Peer) (pid : PeerId)
    (cache clock : List UInt8) (suffix : List HiddenRecord) : World :=
  {w with
    wg := {w.wg with
      dev := some (RetryReady.result (detachedDevice d p pid) pid (detachedPeer p) cache)
      timerPassStep := none}
    ambient := {w.ambient with
      hidden := some suffix
      steps := RetryReady.decisions (detachedPeer p) clock w.ambient.netRxSection w.ambient.steps
      fired := w.ambient.fired.push Worker.timerRetransmit.symbol
      pendingWork := w.ambient.pendingWork.filter (· != Worker.timerRetransmit.index)}}

theorem fire_result_snapshot (w : World) (d : Device) (p : Peer) (pid : PeerId)
    (cache clock : List UInt8) (suffix : List HiddenRecord) :
    Campaign2.Product.snapshot (fireResult w d p pid cache clock suffix) =
      fireView (Campaign2.Product.snapshot w) d p pid cache clock suffix := rfl

end Leanux.Proofs.WG.TimerDiscipline.FireReady
