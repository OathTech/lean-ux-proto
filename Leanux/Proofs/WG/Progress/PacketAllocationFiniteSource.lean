import Leanux.Kernel.Defs

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.ActivationFinite
open Leanux

/-- The packet headroom site is statically lax-zero; it cannot enter the
allocation loop in any allocation/record mode. -/
theorem cowHead_source :
    AmbientM.hiddenAlloc .skbCowHead = pure true := rfl

/-- Checksum help has no recorded allocation in this mirror. -/
theorem checksumHelp_source :
    AmbientM.hiddenAlloc .skbChecksumHelp = pure true := rfl

/-- Transmit copy-on-write has no allocation loop at this concrete site. -/
theorem cowDataTx_source :
    AmbientM.hiddenAlloc .skbCowDataTx = pure true := rfl

/-- Receive copy-on-write has no allocation loop at this concrete site. -/
theorem cowDataRx_source :
    AmbientM.hiddenAlloc .skbCowDataRx = pure true := rfl

end Leanux.Proofs.WG.Progress.ActivationFinite
