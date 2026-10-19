import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeyFrames

/-! The key-index removal exposes its original device read, membership
decision and table writeback. The component's local table computation has
no other WireGuard fields; its actual ambient decision remains in order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
open Leanux Leanux.WG Leanux.Proofs.Framing

def unhashNative (kid : KeypairId) : WG.M Unit := do
  let d←getDev
  _←branch .idxRemoveHashed (d.indexTable.any (·.owner == .keypair kid))
  modifyDev fun current=>{current with indexTable:=d.indexTable.filter fun e=>!(e.owner == .keypair kid)}

/-- The component adapter preserves its missing-device guard and exact
membership decision before writing only the filtered index table. -/
theorem unhash_factor (kid : KeypairId) :
    liftIndex (indexRemove (.keypair kid))=unhashNative kid := by
  funext w a
  change ((liftIndex (indexRemove (.keypair kid))).run w).run a=((unhashNative kid).run w).run a
  rw [liftIndex_run]
  unfold indexRemove
  index_unfold _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry
  simp only [unhashNative,getDev,StateT.run_bind]
  cases device : w.dev with
  | none=>simp [device,invariant,AmbientM.invariant]; rfl
  | some d=>simp [device,branch,modifyDev]; rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
