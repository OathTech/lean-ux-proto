import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointStack

/-! The original held and normal GRO lists are traversed in their source
order. An entry keeps its own packet and candidate scope through each flush. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev toStack := GroOccurrence.stackWith hooks.stackInput (Driver.stackObserved hooks)

noncomputable def normalListShape (buffer : GroOccurrence.Buffer) :
    Shape (GroOccurrence.normalListWith toStack buffer) := by
  unfold GroOccurrence.normalListWith
  split
  · exact .pure _
  · exact .bind (stackListShape _) (fun _ => .pure _)

noncomputable def normalOneShape (buffer : GroOccurrence.Buffer) (entry : GroOccurrence.Entry) (segs : Nat) :
    Shape (GroOccurrence.normalOneWith toStack buffer entry segs) := by
  unfold GroOccurrence.normalOneWith
  dsimp only
  split
  · exact normalListShape _
  · exact .pure _

macro "napi_gro_shape" : tactic => `(tactic| first
  | (napi_shape_head GroOccurrence.normalOneWith; exact normalOneShape _ _ _)
  | (napi_shape_head GroOccurrence.normalListWith; exact normalListShape _)
  | (napi_shape_head ForIn.forIn; apply listShape)
  | napi_stack_shape)

noncomputable def groReceiveShape (buffer : GroOccurrence.Buffer) (entry : GroOccurrence.Entry) :
    Shape (GroOccurrence.receiveWith liftPrefix toStack buffer entry) := by
  apply Shape.marked (.groReceive buffer entry)
  unfold GroOccurrence.receiveWith
  repeat' napi_gro_shape

noncomputable def groFlushShape (buffer : GroOccurrence.Buffer) :
    Shape (GroOccurrence.flushAllWith toStack buffer) := by
  apply Shape.marked (.groFlush buffer)
  unfold GroOccurrence.flushAllWith
  repeat' napi_gro_shape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
