import Leanux.Proofs.WG.Index.TableModel
import Leanux.Proofs.WG.Config.Returns

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem indexRemove_exact (owner : IndexOwner) (d : Device) :
    Returns (indexRemove owner) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some { d with indexTable := removeOwner owner d.indexTable }) := by
  rw [returns_iff]
  noise_vcgen [indexRemove, _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry,
    getDev, getK, branch, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [removeOwner]

theorem indexHashed_exact (owner : IndexOwner) (d : Device) :
    Returns (indexHashed owner) (fun w => w.k.wg = some d)
      (fun hashed w => hashed = d.indexTable.any (·.owner == owner) ∧ w.k.wg = some d) := by
  rw [returns_iff]
  mvcgen [indexHashed, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem indexReplace_exact (pid : PeerId) (kp : KeypairId) (d : Device) :
    Returns (indexReplaceHandshake pid kp) (fun w => w.k.wg = some d)
      (fun hashed w => hashed = d.indexTable.any (·.owner == .handshake pid) ∧
        w.k.wg = some (if hashed then
          { d with indexTable := replaceOwner pid kp d.indexTable } else d)) := by
  rw [returns_iff]
  mvcgen [indexReplaceHandshake, indexHashed, getDev, getK, branch, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [replaceOwner]

end Leanux.Proofs.WG.Index
