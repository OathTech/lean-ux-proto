import AllowedipsProjection
import PeerCountPhase

namespace Binary.AllowedipsRelation
open Leanux Leanux.WG

theorem Physical.frame (c : Config) (raw nextRaw : List MachineState)
    (seen nextSeen : List LookupObservation.Point) (s t : MachineState) (v : View)
    (physical : Physical c raw seen s v)
    (phase : LookupRelation.countPhase nextRaw nextSeen = LookupRelation.countPhase raw seen)
    (writes : Address → Prop) (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ a, Reads c v a → ¬writes a) :
    Physical c nextRaw nextSeen t v := by
  refine ⟨physical.1.frame frame (fun a h => apart a (.inl h)), ?_⟩
  cases focus : c.focus.peer with
  | none => simpa only [Physical, focus] using physical.2
  | some pid =>
    obtain ⟨count, eq, nonnull, loaded⟩ := physical.2 |> (by simpa only [focus] using ·)
    refine ⟨count, eq, nonnull, ?_⟩
    rw [phase]
    exact PeerCountPhase.At.frame frame
      (fun i hi => apart _ (.inr ⟨pid, focus, i, hi, rfl⟩)) loaded

#print axioms Physical.frame
end Binary.AllowedipsRelation
