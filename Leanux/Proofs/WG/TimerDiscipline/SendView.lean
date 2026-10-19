import Leanux.Proofs.WG.Roaming.Model
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
handshake creation's table updates and of the initiation-view interface.
The global optional peer cells retain tags, all key slots and the owner
metadata needed by H1/H2 and remote destinations for H3. The configuration
header, netlink socket and selector table supply H4 readback frames. -/
abbrev WorkQueues := List PeerId × List PeerId
abbrev SendWorkCell := Nat × Option KeypairId × Option KeypairId × Option KeypairId ×
  Nat × Option PeerId × Nat × Bool × Option (Nat × Nat × Nat × Nat)

def sendWorkCell (p : Peer) : SendWorkCell :=
  (p.handshakeState,p.keypairNext,p.keypairPrevious,p.keypairCurrent,
    p.refcount,p.handshakeEntryPeer,p.internalId,p.isDead,p.endpoint.map Roaming.destination)
/-- Device configuration fields unchanged by socket transmission. -/
abbrev SendConfiguration := String × Nat × Nat × Nat × StaticIdentity × Nat
def sendConfiguration (d : Device) : SendConfiguration :=
  (d.ifname,d.ifindex,d.incomingPort,d.fwmark,d.staticIdentity,d.deviceUpdateGen)
abbrev SendSocketContext := NlSock × List (String × Nat × Option String)
abbrev SendWorkDevice := TableCursor × WorkQueues × (PeerId → Option SendWorkCell) ×
  SendConfiguration × SendSocketContext
abbrev SendWorkPeer := InitiationView × Bool × SendWorkCell
abbrev SendWorkView := Option SendWorkDevice × Option SendWorkPeer
abbrev WorkView := Option (List PeerId) × Option Bool
abbrev QueueWorkView := Option WorkQueues × Option Bool

def workQueues (d : Device) : WorkQueues := (d.sendWorkQueue, d.clearWorkQueue)
def sendWorkDevice (sock : NlSock) (devices : List (String × Nat × Option String))
    (d : Device) : SendWorkDevice :=
  (tableCursor d, workQueues d, (fun pid => d.peers[pid]?.map sendWorkCell),
    sendConfiguration d, sock, devices)
def sendWorkPeer (p : Peer) : SendWorkPeer :=
  (initiationView p, p.handshakePending, sendWorkCell p)
def workObservation (s : Snapshot) (pid : PeerId) : WorkView :=
  (s.wg.device.map Device.sendWorkQueue,
    (s.wg.device.bind fun d => d.peers[pid]?).map Peer.handshakePending)

def queueWorkObservation (s : Snapshot) (pid : PeerId) : QueueWorkView :=
  (s.wg.device.map workQueues,
    (s.wg.device.bind fun d => d.peers[pid]?).map Peer.handshakePending)

end Leanux.Proofs.WG.TimerDiscipline
