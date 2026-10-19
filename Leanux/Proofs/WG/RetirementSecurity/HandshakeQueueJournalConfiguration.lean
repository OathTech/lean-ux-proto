import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueJournalTraffic
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueConfiguration
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueLifecycle

/-! Original configuration and lifecycle callbacks carry physical handshake
input validity and the same retained event history. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity
variable {E : Type} {Valid : List UInt8 → Prop} {Safe : List E → Prop}
  {hooks : Driver.Hooks E} {ρ : E → Option TransmitSecurity.Journal.Event}

theorem config_device (c : Contracts Valid Safe hooks ρ) (attrs : DeviceAttrs) :
    StateSafe Valid Safe (Driver.configDevice hooks attrs) := by
  have history : Driver.StateHistorySafe Safe (Driver.configDevice hooks attrs) :=
    (show Driver.configDevice (quietHooks hooks) attrs=Driver.configDevice hooks attrs from rfl) ▸
      Driver.configDevice_history c.quiet attrs
  have projected:=Projection.state (Driver.configDevice_projects c.projects attrs) (Driver.configDevice_projects TransmitSecurity.Journal.hooks_projects attrs)
  rw [Driver.nonce_configDevice_eq] at projected
  exact state_native history projected (Nonce.configDevice_erases attrs) (frame (set_device_cell attrs))

theorem open_device (c : Contracts Valid Safe hooks ρ) : StateSafe Valid Safe (Driver.openObserved hooks) := by
  have history : Driver.StateHistorySafe Safe (Driver.openObserved hooks) :=
    (show Driver.openObserved (quietHooks hooks)=Driver.openObserved hooks from rfl) ▸ Driver.open_history c.quiet
  have projected:=Projection.state (Driver.open_projects c.projects) (Driver.open_projects TransmitSecurity.Journal.hooks_projects)
  rw [Driver.nonce_openObserved_eq] at projected
  exact state_native history projected Nonce.openObserved_erases (frame open_cell)

theorem up (c : Contracts Valid Safe hooks ρ) : StateSafe Valid Safe (Driver.upObserved hooks) := by
  have history : Driver.StateHistorySafe Safe (Driver.upObserved hooks) :=
    (show Driver.upObserved (quietHooks hooks)=Driver.upObserved hooks from rfl) ▸ Driver.up_history c.quiet
  have projected:=Projection.state (Driver.up_projects c.projects) (Driver.up_projects TransmitSecurity.Journal.hooks_projects)
  rw [Driver.nonce_upObserved_eq] at projected
  exact state_native history projected Nonce.upObserved_erases (frame up_cell)

theorem down (c : Contracts Valid Safe hooks ρ) : StateSafe Valid Safe (Driver.downObserved hooks) := by
  have history : Driver.StateHistorySafe Safe (Driver.downObserved hooks) :=
    (show Driver.downObserved (quietHooks hooks)=Driver.downObserved hooks from rfl) ▸ Driver.down_history c.quiet
  have projected:=Projection.state (Driver.down_projects c.projects) (Driver.down_projects TransmitSecurity.Journal.hooks_projects)
  rw [Driver.down_lift Driver.nonceHooks rfl rfl] at projected
  exact state_native history projected (erasesStatePrefix_lift _) (frame down_cell)

theorem destroy (c : Contracts Valid Safe hooks ρ) : StateSafe Valid Safe (Driver.destructObserved hooks) := by
  have history : Driver.StateHistorySafe Safe (Driver.destructObserved hooks) :=
    (show Driver.destructObserved (quietHooks hooks)=Driver.destructObserved hooks from rfl) ▸ Driver.destruct_history c.quiet
  have projected:=Projection.state (Driver.destruct_projects c.projects) (Driver.destruct_projects TransmitSecurity.Journal.hooks_projects)
  rw [Driver.destruct_lift Driver.nonceHooks rfl rfl] at projected
  exact state_native history projected (erasesStatePrefix_lift _) (destruct Valid)

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
