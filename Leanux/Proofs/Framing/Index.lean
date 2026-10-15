import Leanux.WG.Peer

/-! Exact source equations for the index-unhash action, including its getter
failure and recorded decision. No device-presence premise is added. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG

def indexUnhash (d : Decision) (hashed : IndexEntry → Bool) : M Unit := do
  _ ← branch d ((← getDev).indexTable.any hashed)
  modifyDev fun dev => { dev with indexTable := dev.indexTable.filter fun e => !hashed e }

theorem indexRemove_eq (owner : IndexOwner) :
    indexRemove owner = indexUnhash .idxRemoveHashed
      (fun e => e.owner == owner) := rfl

end Leanux.Proofs.Framing
