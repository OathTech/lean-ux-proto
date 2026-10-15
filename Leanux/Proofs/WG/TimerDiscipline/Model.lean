import Leanux.Proofs.WG.TimerDiscipline.View
import Leanux.WG.Timers

/-! Pure timer observations, arithmetic, records and store transformations. -/
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

def nextAttempts (attempts : Nat) : Nat :=
  if attempts > MAX_TIMER_HANDSHAKES then attempts else attempts + 1

inductive JitterSite where
  | retransmit
  | newHandshake

def JitterSite.hiddenSite : JitterSite → HiddenSite
  | .retransmit => .retransmitJitter
  | .newHandshake => .newHandshakeJitter

def jitterRecord (site : JitterSite) (byte : UInt8) : HiddenRecord :=
  { site := site.hiddenSite.info.id, bytes := [byte, 0, 0, 0, 0, 0, 0, 0] }

abbrev jitterAccepted (byte : UInt8) : Prop :=
  (HZ / 3 * byte.toNat) % 256 ≥ 256 % (HZ / 3)

def jitterValue (byte : UInt8) : Nat := HZ / 3 * byte.toNat / 256

def jitterStream (site : JitterSite) (rejected : List UInt8) (accepted : UInt8)
    (rest : List HiddenRecord) := rejected.map (jitterRecord site) ++ jitterRecord site accepted :: rest

def giveUpPeer (p : Peer) : Peer :=
  { (p.setTimer .sendKeepalive none) with staged := [] }

def duePeers (d : Device) (timer : PeerTimer) (jHi : UInt64) : List PeerId :=
  d.peerList.filter fun pid => match d.peers.get? pid >>= (·.timer timer) with
    | some expiry => timeBefore expiry jHi
    | none => false

def giveUpDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  { d with
    peers := (d.peers.insert pid (p.setTimer .sendKeepalive none)).insert pid (giveUpPeer p)
    txDropped := d.txDropped + p.staged.length }

end Leanux.Proofs.WG.TimerDiscipline
