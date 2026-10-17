import Leanux.Proofs.WG.Noise.InitiationReadyModel
import Leanux.Proofs.WG.Config.Returns

/-! Exact native peer writes used by the initiation stages. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

abbrev setChain := noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain

theorem chain_returns (pid : PeerId) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (ck hash : List UInt8) (records : Option (List HiddenRecord)) (g : WGWorld) :
    Config.Product.Returns ((setChain pid ck hash).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = records)
      (fun (_, current) ambient => current.dev = some (chainDevice pid d p ck hash) ∧ ambient.hidden = records) := by
  intro ambient pre
  refine ⟨((), {g with dev := some (chainDevice pid d p ck hash)}), ambient, ?_, rfl, pre.2⟩
  change (((do setPeer pid {(← getPeer pid) with chainingKey := ck, hash} : WG.M Unit).run g).run ambient) = _
  simp [getPeer, getDev, pre.1, resident, setPeer, modifyDev, chainDevice]
  rfl

def setSecret (pid : PeerId) (secret : List UInt8) : WG.M Unit := do
  setPeer pid {(← getPeer pid) with ephemeralPrivate := secret}

theorem setSecret_returns (pid : PeerId) (secret : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (records : Option (List HiddenRecord)) (g : WGWorld) :
    Config.Product.Returns ((setSecret pid secret).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = records)
      (fun (_, current) ambient => current.dev = some (secretDevice pid d p secret) ∧ ambient.hidden = records) := by
  intro ambient pre
  refine ⟨((), {g with dev := some (secretDevice pid d p secret)}), ambient, ?_, rfl, pre.2⟩
  simp [setSecret, getPeer, getDev, pre.1, resident, setPeer, modifyDev, secretDevice]
  rfl

end Leanux.Proofs.WG.Noise.InitiationReady
