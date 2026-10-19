import Leanux.WG.Send

/-! The native keepalive prefix, before any staged-send continuation. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
open Leanux Leanux.WG

def keepalivePrepare (pid : PeerId) : WG.M Bool := do
  let p ← getPeer pid
  if ← branch .keepaliveStagedEmpty p.staged.isEmpty then
    if ← branch .keepaliveNoMem !(← hiddenAlloc .keepaliveSkb) then return false
    setPeer pid { p with staged := p.staged ++ [{ mtu := (← getDev).mtu }] }
  pure true

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
