import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Leanux.Proofs.WG.Campaign2.Bridge
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- The original keepalive caller with finite allocation. Its staging, nonce,
queueing and release suffixes are the original finite traversals. -/
def keepalive (pid : PeerId) : WG.M Unit := do
  let p ← getPeer pid
  if ← branch .keepaliveStagedEmpty p.staged.isEmpty then
    -- `alloc_skb(DATA_PACKET_HEAD_ROOM + MESSAGE_MINIMUM_LENGTH, GFP_ATOMIC)`
    -- (send.c:226): NULL returns without staging or sending (send.c:228-229)
    if ← branch .keepaliveNoMem !(← monadLift (hiddenAllocFinite .keepaliveSkb)) then return
    -- `PACKET_CB(skb)->mtu = skb->dev->mtu` (W4: `Device.mtu`; Data.lean pads with it)
    setPeer pid { p with staged := p.staged ++ [{ mtu := (← getDev).mtu }] }
  sendStagedPackets pid

theorem keepalive_source (pid : PeerId) : WG.sendKeepalive pid = keepalive pid := by
  unfold WG.sendKeepalive keepalive
  have allocation : (hiddenAlloc .keepaliveSkb : WG.M Bool) =
      monadLift (hiddenAllocFinite .keepaliveSkb) := by
    change monadLift (AmbientM.hiddenAlloc .keepaliveSkb) = _
    rw [hiddenAlloc_finite_source]
  rw [allocation]

end Leanux.Proofs.WG.Progress.HandshakeFinite
