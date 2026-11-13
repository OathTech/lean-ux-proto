import Leanux.Kernel.Defs

/-! Optional observation of original source execution. These operations
only append diagnostic output; they neither consume records nor supply
values or decisions to the operational mirror. -/

namespace Leanux.Observation

def replacementEntry (peer : WG.PeerId) (keypair : WG.KeypairId) : WG.M Unit := do
  let ambient ← getAmbient
  match ambient.replacementEntries with
  | none => pure ()
  | some entries =>
    let wg ← get
    let entry : ReplacementEntryObservation := {
      peer, keypair, device := wg.dev, peerCounter := wg.peerCounter,
      keypairCounter := wg.keypairCounter, hidden := ambient.hidden,
      steps := ambient.steps, netRxSection := ambient.netRxSection,
      suspended := ambient.suspended, pendingWork := ambient.pendingWork,
      unitPeers := ambient.unitPeers }
    modifyAmbient fun a => { a with replacementEntries := some (entries.push entry) }

end Leanux.Observation
