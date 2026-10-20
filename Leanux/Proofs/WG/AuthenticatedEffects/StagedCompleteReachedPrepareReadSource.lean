import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadAccessSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSkbAccessSource

/-! Observed getter interiors retain the native suffix and the original
access receipt. The packet-store read includes its explicit adapter write-back. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

noncomputable def keyReadSource (id : KeypairId) : ReadAccess.Shape (getKeypair id) := by
  simp only [getKeypair,getDev,invariant]
  repeat' readonly_source_step

inductive ReadPoint : {E α : Type} → {body : WGPrefix E α} → Access body →
    WGWorld → Ambient → WGWorld → Ambient → Prop where
  | peer (point : ReadAccess.Point (ReadAccess.peerShape pid) w a v b) :
      ReadPoint (.readPeer pid) w a v b
  | key {id : KeypairId} (point : ReadAccess.Point (keyReadSource id) w a v b) :
      ReadPoint (.readKey id) w a v b
  | rx {id : SkbId} (point : SkbAccess.Point (SkbStore.getRx id) w a v b) :
      ReadPoint (.readRx id) w a v b

theorem ReadPoint.remaining {E α : Type} {body : WGPrefix E α} {token : Access body}
    (point : ReadPoint token w a v b) :
    ∃ rest : WG.M α, (token.native.run w).run a = (rest.run v).run b := by
  cases point with
  | peer point => exact point.remaining
  | key point => exact point.remaining
  | rx point => exact point.remaining

def accessSuffix {E α : Type} {body : WGPrefix E α} (token : Access body)
    (original : WGWorld) (rest : WG.M α) : WGPrefix E α :=
  fun w a => ExceptT.mk fun h => match (rest.run w).run a with
    | .error reason => (Except.error (α:=((α × WGWorld) × Ambient)) reason,h)
    | .ok ((value,v),b) => (.ok ((value,v),b),h ++ token.events original value)

noncomputable def ReadPoint.remainder {E α : Type} {body : WGPrefix E α} {token : Access body}
    (point : ReadPoint token w a v b) : WGPrefix E α :=
  accessSuffix token w (Classical.choose point.remaining)

theorem ReadPoint.remainder_run {E α : Type} {body : WGPrefix E α} {token : Access body}
    (point : ReadPoint token w a v b) (h : List E) :
    runWGPrefix body w a h = runWGPrefix point.remainder v b h := by
  rw [token.run]
  exact congrArg (fun result : Except Stop ((α × WGWorld) × Ambient) => match result with
    | .error reason => (Except.error (α:=((α × WGWorld) × Ambient)) reason,h)
    | .ok ((value,next),ambient) => (Except.ok (ε:=Stop) ((value,next),ambient),h ++ token.events w value))
    (Classical.choose_spec point.remaining)

theorem ReadPoint.remainder_appends {E α : Type} {body : WGPrefix E α} {token : Access body}
    (point : ReadPoint token w a v b) : StateAppends point.remainder := by
  intro u c h
  change ∃ suffix, (match ((Classical.choose point.remaining).run u).run c with
    | .error reason => (Except.error (α:=((α × WGWorld) × Ambient)) reason,h)
    | .ok ((value,next),ambient) => (Except.ok (ε:=Stop) ((value,next),ambient),h ++ token.events w value)).2 = h ++ suffix
  split
  · exact ⟨[],(List.append_nil h).symm⟩
  · exact ⟨_,rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
