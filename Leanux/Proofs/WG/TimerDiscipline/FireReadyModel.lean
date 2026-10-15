import Leanux.Proofs.WG.TimerDiscipline.RetryReadyModel

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

def detachedDevice (d : Device) (p : Peer) (pid : PeerId) : Device :=
  {d with peers := d.peers.insert pid (p.setTimer .retransmitHandshake none)}
def suppliedRecords (start cache clock queue stop : List UInt8) (suffix : List HiddenRecord) : List HiddenRecord :=
  sectionRecord true start :: {site:=150,bytes:=cache} :: {site:=6,bytes:=clock} ::
    {site:=(HiddenSite.queued .sendWorker).info.id,bytes:=queue} :: sectionRecord false stop :: suffix
def fireView (entry : Campaign2.Snapshot) (d : Device) (p : Peer) (pid : PeerId)
    (cache clock : List UInt8) (suffix : List HiddenRecord) : Campaign2.Snapshot :=
  {entry with
    wg := {entry.wg with
      device := some (RetryReady.result (detachedDevice d p pid) pid
        (p.setTimer .retransmitHandshake none) cache)
      queuedThisCall := pid :: entry.wg.queuedThisCall}
    ambient := {entry.ambient with
      hidden := some suffix
      steps := RetryReady.decisions (p.setTimer .retransmitHandshake none) clock
        entry.ambient.netRxSection entry.ambient.steps
      fired := entry.ambient.fired.push Worker.timerRetransmit.symbol
      pendingWork := entry.ambient.pendingWork.filter (· != Worker.timerRetransmit.index)}}

end Leanux.Proofs.WG.TimerDiscipline.FireReady
