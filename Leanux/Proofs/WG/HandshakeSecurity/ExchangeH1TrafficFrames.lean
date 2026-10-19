import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1ConfigurationFrames

/-! Native ingress, transmit and outer leaf projections from C2 H1. Each field
is a normal-return operational tag fact pinned at `5177bd9c`, never an exchange
history or reachability assumption. Native shutdown/deletion is deliberately
absent: its queued sends are observed by the shared driver. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Lifetimes Queues

structure H1TrafficTagFrames : Prop where
  /-- C2 `Noise.DriverTags.Traffic.receive_retained`, pin `5177bd9c`,
  instantiated at the actual entry tag map. -/
  receive : ∀ msg src, H1TagRetains (wgReceive msg src)
  /-- C2 `Noise.DriverTags.Transmit.retained`, pin `5177bd9c`. -/
  transmit : ∀ family addr packets mtu, H1TagRetains (wgXmit family addr packets mtu)
  /-- C2 `Noise.DriverTags.Dump.retained`, pin `5177bd9c`. -/
  dump : ∀ action : NetlinkDumpCall, H1TagRetains action.original
  /-- C2 `Noise.DriverTags.Environment.create_native`, pin `5177bd9c`,
  instantiated at the actual entry tag map. -/
  create : H1TagRetains WG.wgCreate
  /-- C2 `Noise.DriverTags.Environment.cleanup_native`, pin `5177bd9c`,
  instantiated at the actual entry tag map. This source performs netnsPreExit,
  not shutdown or a queued-send drain. -/
  cleanup : H1ProductTagRetains Env.netnsCleanup

end Leanux.Proofs.WG.HandshakeSecurity
