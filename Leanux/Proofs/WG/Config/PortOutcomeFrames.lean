import Leanux.Proofs.WG.Config.PortOutcomeModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- The pure port outcome changes only sockets, incoming port and generation;
all peer/node and selector data stay exactly those of the original Device. -/
theorem nonzeroPortRequestOutcome_frame (d : Device) (port : Nat) (bound : Nat → Bool) :
    {(nonzeroPortRequestOutcome d port bound).2 with
      incomingPort := d.incomingPort,
      sock4 := d.sock4, sock6 := d.sock6, deviceUpdateGen := d.deviceUpdateGen} = d := by
  unfold nonzeroPortRequestOutcome
  split
  · rfl
  · unfold portOutcome
    split
    · rfl
    · unfold socketOutcome
      split
      · rfl
      · split <;> rfl

end Leanux.Proofs.WG.Config
