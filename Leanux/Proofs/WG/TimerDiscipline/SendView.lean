import Leanux.Proofs.WG.TimerDiscipline.View

/-! Pure observations preserved by socket sending, not by handshake creation. -/
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

abbrev TableCursor := List IndexEntry × Nat
abbrev SendView := Option TableCursor × Option InitiationView

def tableCursor (d : Device) : TableCursor := (d.indexTable, d.nextKeypairId)

def sendObservation (s : Snapshot) (pid : PeerId) : SendView :=
  (s.wg.device.map tableCursor, initiationObservation s pid)

end Leanux.Proofs.WG.TimerDiscipline
