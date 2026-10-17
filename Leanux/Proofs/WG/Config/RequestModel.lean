import Leanux.WG.Types

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

def requestGeneration (d : Device) : Device :=
  { d with deviceUpdateGen := d.deviceUpdateGen + 1 }

end Leanux.Proofs.WG.Config
