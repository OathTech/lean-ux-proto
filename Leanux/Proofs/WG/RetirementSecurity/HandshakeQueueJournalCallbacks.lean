import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueJournalBase
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueMaintenance
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueCrypto

/-! Source-derived queue validity and conditional history safety through
native callbacks. The actual handshake worker remains separately checked. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity
variable {E : Type} {Valid : List UInt8 → Prop} {Safe : List E → Prop}
  {hooks : Driver.Hooks E} {ρ : E → Option Nonce.Allocation}

theorem staging (c : Contracts Valid Safe hooks ρ) (pid : PeerId) :
    StateSafe Valid Safe (Driver.stagingObserved hooks pid) := by
  have history : Driver.StateHistorySafe Safe (Driver.stagingObserved hooks pid) := c.quiet.staging pid
  have projected:=Driver.staging_projects c.projects pid
  rw [Driver.nonce_staging_specialization] at projected
  exact state_native history projected (Nonce.stagingObserved_erases pid) (frame (sendStagedPackets_cell pid))

theorem keepalive (c : Contracts Valid Safe hooks ρ) (pid : PeerId) :
    StateSafe Valid Safe (Driver.keepaliveObserved hooks pid) := by
  have history : Driver.StateHistorySafe Safe (Driver.keepaliveObserved hooks pid) :=
    Driver.keepalive_actor_history c.quiet.toActorCoreHistorySafe pid
  have projected:=Driver.keepalive_projects c.projects pid
  rw [Driver.nonce_keepaliveObserved_eq] at projected
  exact state_native history projected (Nonce.keepaliveObserved_erases pid) (frame (sendKeepalive_cell pid))

theorem timer (c : Contracts Valid Safe hooks ρ) (pid : PeerId) (timer : PeerTimer) :
    StateSafe Valid Safe (Driver.timerObserved hooks pid timer) := by
  have history : Driver.StateHistorySafe Safe (Driver.timerObserved hooks pid timer) :=
    Driver.timer_history c.quiet.toActorCoreHistorySafe pid timer
  have projected:=Driver.timer_projects c.projects pid timer
  rw [Driver.nonce_timerObserved_eq] at projected
  exact state_native history projected (Nonce.timerObserved_erases pid timer) (frame (timer_cell pid timer))

theorem session (c : Contracts Valid Safe hooks ρ) (pid : PeerId) :
    StateSafe Valid Safe (hooks.session pid) :=
  state_native (c.quiet.session pid) (c.projects.session pid) (erasesStatePrefix_lift _)
    (frame (beginSession_cell pid))

theorem confirmation (c : Contracts Valid Safe hooks ρ) (pid : PeerId) (kid : KeypairId) :
    StateSafe Valid Safe (hooks.confirmation pid kid) :=
  state_native (c.quiet.confirmation pid kid) (c.projects.confirmation pid kid) (erasesStatePrefix_lift _)
    (frame (receivedWithKeypair_cell pid kid))

theorem transmit (c : Contracts Valid Safe hooks ρ) (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe Valid Safe (Driver.transmitObserved hooks family addr packets mtu) := by
  have history : Driver.StateHistorySafe Safe (Driver.transmitObserved hooks family addr packets mtu) :=
    Driver.transmit_history c.quiet.toActorCoreHistorySafe family addr packets mtu
  have projected:=Driver.transmit_projects c.projects family addr packets mtu
  rw [Driver.nonce_transmitObserved_eq] at projected
  exact state_native history projected (Nonce.transmitObserved_erases family addr packets mtu)
    (frame (wgXmit_cell family addr packets mtu))

theorem softirq (c : Contracts Valid Safe hooks ρ) :
    ProductSafe Valid Safe (Driver.softirqObserved hooks) := by
  have history : Driver.ProductHistorySafe Safe (Driver.softirqObserved hooks) :=
    (show Driver.softirqObserved (quietHooks hooks)=Driver.softirqObserved hooks from rfl) ▸ Driver.softirq_history c.quiet
  have projected:=Driver.softirq_projects c.projects
  rw [Driver.nonce_softirqObserved_eq] at projected
  exact product_native history projected Nonce.softirqObserved_erases (product_frame napiSoftirq_cell)

theorem irqExit (c : Contracts Valid Safe hooks ρ) :
    ProductSafe Valid Safe (Driver.irqExitObserved hooks) := by
  have history : Driver.ProductHistorySafe Safe (Driver.irqExitObserved hooks) :=
    (show Driver.irqExitObserved (quietHooks hooks)=Driver.irqExitObserved hooks from rfl) ▸ Driver.irqExit_history c.quiet
  have projected:=Driver.irqExit_projects c.projects
  rw [Driver.nonce_irqExitObserved_eq] at projected
  exact product_native history projected Nonce.irqExitObserved_erases (product_frame napiIrqExit_cell)

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
