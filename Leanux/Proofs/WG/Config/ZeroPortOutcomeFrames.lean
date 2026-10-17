import Leanux.Proofs.WG.Config.ZeroPortOutcomeModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Zero-port selection changes only the port/socket fields beyond generation;
peer/node, selector, header capacity and allowed-IP sequence inputs are preserved. -/
theorem zeroPortRequestDevice_frame (d : Device) (chosen : Nat) :
    {zeroPortRequestDevice d chosen with
      incomingPort := d.incomingPort, sock4 := d.sock4, sock6 := d.sock6} = requestGeneration d := by
  unfold zeroPortRequestDevice
  split
  · rfl
  · split <;> rfl

end Leanux.Proofs.WG.Config
