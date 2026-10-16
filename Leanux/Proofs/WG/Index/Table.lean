import Leanux.Proofs.WG.Index.TableModel
import Leanux.Proofs.WG.Config.Returns

set_option autoImplicit false
set_option pp.structureInstances false

/-! The original device-level contracts enter the native index component through
its actual guarded adapter. Every ambient input is quantified; the existing
resident-device premise is retained, without a new table-validity premise. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem indexRemove_exact (owner : IndexOwner) (d : Device) :
    Returns (liftIndex (indexRemove owner)) (fun g => g.dev = some d)
      (fun _ g => g.dev = some {d with indexTable := removeOwner owner d.indexTable}) := by
  intro g ambient device
  let final := {g with dev := some {d with indexTable := removeOwner owner d.indexTable}}
  let ambient' := {ambient with steps := ambient.steps.push {
    decision := .idxRemoveHashed, outcome := d.indexTable.any (·.owner == owner),
    netRx := ambient.netRxSection}}
  refine ⟨(), final, ambient', ?_, rfl⟩
  let action : IndexM Unit := do
    _ ← branch .idxRemoveHashed ((← get).any (·.owner == owner))
    modify fun table => table.filter (fun e => !(e.owner == owner))
  change ((liftIndex action).run g).run ambient = _
  simp [action, liftIndex, getDev, device, branch, AmbientM.branch, modifyDev,
    removeOwner, final, ambient']
  rfl

theorem indexHashed_exact (owner : IndexOwner) (d : Device) :
    Returns (liftIndex (indexHashed owner)) (fun g => g.dev = some d)
      (fun hashed g => hashed = d.indexTable.any (·.owner == owner) ∧ g.dev = some d) := by
  intro g ambient device
  refine ⟨d.indexTable.any (·.owner == owner), {g with dev := some d}, ambient, ?_, rfl, rfl⟩
  simp [liftIndex, indexHashed, getDev, device, modifyDev]
  rfl

theorem indexReplace_exact (pid : PeerId) (kp : KeypairId) (d : Device) :
    Returns (liftIndex (indexReplaceHandshake pid kp)) (fun g => g.dev = some d)
      (fun hashed g => hashed = d.indexTable.any (·.owner == .handshake pid) ∧
        g.dev = some (if hashed then
          {d with indexTable := replaceOwner pid kp d.indexTable} else d)) := by
  intro g ambient device
  let hashed := d.indexTable.any (·.owner == .handshake pid)
  let final := {g with dev := some (if hashed then
    {d with indexTable := replaceOwner pid kp d.indexTable} else d)}
  let ambient' := {ambient with steps := ambient.steps.push {
    decision := .idxReplaceUnhashed, outcome := !hashed, netRx := ambient.netRxSection}}
  refine ⟨hashed, final, ambient', ?_, rfl, rfl⟩
  cases found : d.indexTable.any (·.owner == .handshake pid) <;>
    simp [liftIndex, indexReplaceHandshake, indexHashed, getDev, device,
      branch, AmbientM.branch, modifyDev, found, hashed, final, ambient', replaceOwner,
      -List.any_eq_false]
  all_goals rfl

end Leanux.Proofs.WG.Index
