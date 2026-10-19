import Leanux.Proofs.WG.HandshakeSecurity.ExchangeReceive
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeQuietNative
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1DataFrames

/-! Source-carrier composition with operational native data frames. Quiet
native equalities retain the exact journal, rather than identifying unrelated
histories from matching erased endpoints. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem staging_checked (frames : H1DataTagFrames) (pid : PeerId) :
    Preserves (Driver.stagingObserved ExchangeDriver.hooks pid) := by
  rw [ExchangeDriver.staging_lift]
  exact lift _ (fun h => frame h _ (frames.staging pid))

theorem keepalive_checked (frames : H1DataTagFrames) (pid : PeerId) :
    Preserves (Driver.keepaliveObserved ExchangeDriver.hooks pid) := by
  rw [ExchangeDriver.keepalive_lift]
  exact lift _ (fun h => frame h _ (frames.keepalive pid))

theorem consume_checked (frames : H1DataTagFrames) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Preserves (Driver.consumeObserved ExchangeDriver.hooks pid pkt ep) := by
  rw [ExchangeDriver.consume_lift]
  exact lift _ (fun h => frame h _ (frames.consume pid pkt ep))

/-- Both actual session installations and staged keepalives are discharged
at this shared-driver receive worker, with no callback-safety premise. -/
theorem handshake_checked (H1 : H1ExchangeEdges) (handshake : H1HandshakeTagFrames)
    (data : H1DataTagFrames) : Preserves (Driver.handshakeObserved ExchangeDriver.hooks) :=
  receive_worker_checked H1 handshake session
    (Driver.keepaliveObserved ExchangeDriver.hooks) (session_checked H1) (keepalive_checked data)

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
