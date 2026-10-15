import Leanux.Proofs.WG.Config.ScalarSocketReadbackSource

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- The original scalar set followed by the original socket get reads back
the updated scalars and unchanged ordered IPv4 list across two actual chunks.
A later malformed peer returns EINVAL without undoing the first update.
The singleton, stopped-device and two-chunk capacity premises are explicit. -/
theorem scalarSocketReadback_returns (d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid])
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (listed : p.allowedipsList = front ++ b :: tail) (nonempty : front ≠ [])
    (absent : b ∉ front) (readable : Ipv4Residents d nodes (front ++ b :: tail))
    (endpoint : p.endpoint = none)
    (firstFits : devicePrefixSpace d + 140 + 28 * front.length ≤ NLMSG_GOODSIZE)
    (firstFull : NLMSG_GOODSIZE < devicePrefixSpace d + 140 + 28 * (front.length + 1))
    (lastFits : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun w => w.wg.device = some d ∧ w.wg.nlSock7 = sock ∧ ClaimView.selectsDevice w d)
      (fun result w =>
        let updated := scalarRequestDevice d pid p psk interval
        let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        result = ((if bad then -EINVAL else 0),
          .ok (suffixJson updated configured nodes (front ++ b :: tail))) ∧
        w.wg.device = some updated ∧ w.wg.nlSock7 = socketReadbackFinal sock updated) :=
  scalarSocketReadback_source d key psk interval bad pid p nodes front b tail sock peers found resident
    live bounded down listed nonempty absent readable endpoint firstFits firstFull lastFits idle empty

end Leanux.Proofs.WG.Config
