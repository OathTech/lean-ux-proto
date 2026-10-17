import Leanux.Proofs.WG.TimerDiscipline.FireSectionModel

/-! Exact Product observation of the current selected wheel unit. The outer wheel selection is a separate obligation. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.FireReady
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.TimerDiscipline
def suppliedRecords (start cache clock queue stop : List UInt8) (suffix : List HiddenRecord) : List HiddenRecord :=
  sectionRecord true start :: {site:=150,bytes:=cache} :: {site:=6,bytes:=clock} ::
    {site:=(HiddenSite.queued .sendWorker).info.id,bytes:=queue} :: sectionRecord false stop :: suffix

def fireView (entry : Campaign2.Product.Snapshot) (d : Device) (p : Peer) (pid : PeerId)
    (cache clock : List UInt8) (suffix : List HiddenRecord) : Campaign2.Product.Snapshot :=
  {entry with
    wg := {entry.wg with
      device := some (RetryReady.result (detachedDevice d p pid) pid (detachedPeer p) cache)
      timerPassStep := none}
    ambient := {entry.ambient with
      hidden := some suffix
      steps := RetryReady.decisions (detachedPeer p) clock entry.ambient.netRxSection entry.ambient.steps
      fired := entry.ambient.fired.push Worker.timerRetransmit.symbol
      pendingWork := entry.ambient.pendingWork.filter (· != Worker.timerRetransmit.index)}}


end Leanux.Proofs.WG.TimerDiscipline.FireReady
