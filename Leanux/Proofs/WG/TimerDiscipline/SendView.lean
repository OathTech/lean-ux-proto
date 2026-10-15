import Leanux.Proofs.WG.TimerDiscipline.View

/-! Pure observations preserved by socket sending, not by handshake creation. -/
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

abbrev TableCursor := List IndexEntry × Nat
abbrev SendView := Option TableCursor × Option InitiationView

def tableCursor (d : Device) : TableCursor := (d.indexTable, d.nextKeypairId)

def sendObservation (s : Snapshot) (pid : PeerId) : SendView :=
  (s.wg.device.map tableCursor, initiationObservation s pid)

/-- Socket-local extension: queue and selected pending flag are independent of
handshake creation's table updates and of the initiation-view interface. -/
abbrev WorkQueues := List PeerId × List PeerId
abbrev SendWorkDevice := TableCursor × WorkQueues
abbrev SendWorkPeer := InitiationView × Bool
abbrev SendWorkView := Option SendWorkDevice × Option SendWorkPeer
abbrev WorkView := Option (List PeerId) × Option Bool
abbrev QueueWorkView := Option WorkQueues × Option Bool

def workQueues (d : Device) : WorkQueues := (d.sendWorkQueue, d.clearWorkQueue)
def sendWorkDevice (d : Device) : SendWorkDevice := (tableCursor d, workQueues d)
def sendWorkPeer (p : Peer) : SendWorkPeer := (initiationView p, p.handshakePending)
def workObservation (s : Snapshot) (pid : PeerId) : WorkView :=
  (s.wg.device.map Device.sendWorkQueue,
    (s.wg.device.bind fun d => d.peers[pid]?).map Peer.handshakePending)

def queueWorkObservation (s : Snapshot) (pid : PeerId) : QueueWorkView :=
  (s.wg.device.map workQueues,
    (s.wg.device.bind fun d => d.peers[pid]?).map Peer.handshakePending)

end Leanux.Proofs.WG.TimerDiscipline
