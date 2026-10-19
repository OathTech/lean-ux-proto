import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceWitness

/-! The native held/normal GRO paths can call the stack only with an occurrence
witness supplied for that very packet. An older held packet keeps its witness
when the current candidate causes it to flush. Refusals retain the safe prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

private theorem old_then (good : Entry → List E → Prop) (mono : MonotoneWitness good)
    (Safe : List E → Prop) (callback : List Entry → PrefixM E Unit)
    (checked : ∀ entries, PrefixEnsures
      (fun h _ => Safe h ∧ ∀ entry ∈ entries, good entry h) Safe (callback entries)
      (fun _ h _ => Safe h)) (gro : Buffer) (entry held : Entry) (member : held ∈ gro.held)
    (next : Buffer → PrefixM E Buffer)
    (tail : ∀ buffer, PrefixEnsures (fun h _ => (Safe h ∧ buffer.Ready good h) ∧ good entry h)
      Safe (next buffer) (fun output h _ => Safe h ∧ output.Ready good h)) :
    PrefixEnsures (fun h _ => (Safe h ∧ gro.Ready good h) ∧ good entry h) Safe
      (normalOneWith callback {gro with held := []} held 1 >>= next)
      (fun output h _ => Safe h ∧ output.Ready good h) := by
  apply PrefixEnsures.bind _ tail
  apply (remember _ (normalOne_checked good mono Safe callback checked _ held 1)
    (good entry) (fun history suffix => mono entry history suffix)).consequence
  · intro _ _ input
    exact ⟨⟨⟨input.1.1,input.1.2.clearHeld⟩,input.1.2.2 held member⟩,input.2⟩
  · intro _ _ _ output; exact output

theorem receive_checked (good : Entry → List E → Prop) (mono : MonotoneWitness good)
    (Safe : List E → Prop) (callback : List Entry → PrefixM E Unit)
    (checked : ∀ entries, PrefixEnsures
      (fun h _ => Safe h ∧ ∀ entry ∈ entries, good entry h) Safe (callback entries)
      (fun _ h _ => Safe h)) (gro : Buffer) (entry : Entry) :
    PrefixEnsures (fun h _ => (Safe h ∧ gro.Ready good h) ∧ good entry h) Safe
      (receiveWith liftPrefix callback gro entry)
      (fun output h _ => Safe h ∧ output.Ready good h) := by
  have held_pure (g : Buffer) :
      PrefixEnsures (fun h _ => (Safe h ∧ g.Ready good h) ∧ good entry h) Safe
        (pure ({g with held := [entry]} : Buffer) : PrefixM E Buffer)
        (fun output h _ => Safe h ∧ output.Ready good h) :=
    PrefixEnsures.pure (fun _ _ input => input.1.1)
      (fun _ _ input => ⟨input.1.1,input.1.2.hold input.2⟩)
  have append_pure (g : Buffer) :
      PrefixEnsures (fun h _ => (Safe h ∧ g.Ready good h) ∧ good entry h) Safe
        (pure ({g with held := g.held ++ [entry]} : Buffer) : PrefixM E Buffer)
        (fun output h _ => Safe h ∧ output.Ready good h) :=
    PrefixEnsures.pure (fun _ _ input => input.1.1)
      (fun _ _ input => ⟨input.1.1,input.1.2.appendHeld input.2⟩)
  have stopped {α : Type} (message : String) (next : α → PrefixM E Buffer) :
      PrefixEnsures (fun h _ => (Safe h ∧ gro.Ready good h) ∧ good entry h) Safe
        (liftPrefix (unsupported message : Leanux.M α) >>= next)
        (fun output h _ => Safe h ∧ output.Ready good h) := by
    intro w h input
    exact ⟨[],by change h = h ++ []; simp,input.1.1,True.intro⟩
  have stopped_end (message : String) :
      PrefixEnsures (fun h _ => (Safe h ∧ gro.Ready good h) ∧ good entry h) Safe
        (liftPrefix (unsupported message : Leanux.M Buffer))
        (fun output h _ => Safe h ∧ output.Ready good h) := by
    intro w h input
    exact ⟨[],by simp,input.1.1,True.intro⟩
  unfold receiveWith
  repeat' first
    | exact normalOne_checked good mono Safe callback checked _ entry 1
    | exact held_pure _
    | exact append_pure _
    | exact stopped _ _
    | exact stopped_end _
    | (apply old_then good mono Safe callback checked gro entry _ (by simp_all) _)
    | (with_reducible apply PrefixEnsures.ite)
    | (with_reducible intro x; try dsimp only)
    | (split; all_goals try simp_all only [])

private theorem flush_entries_checked (good : Entry → List E → Prop) (mono : MonotoneWitness good)
    (Safe : List E → Prop) (callback : List Entry → PrefixM E Unit)
    (checked : ∀ entries, PrefixEnsures
      (fun h _ => Safe h ∧ ∀ entry ∈ entries, good entry h) Safe (callback entries)
      (fun _ h _ => Safe h)) (entries : List Entry) (gro : Buffer) :
    PrefixEnsures (fun h _ => (Safe h ∧ gro.Ready good h) ∧ ∀ entry ∈ entries, good entry h) Safe
      (forIn entries gro (fun entry g => do
        let next ← normalOneWith callback g entry 1
        pure (.yield next)))
      (fun output h _ => Safe h ∧ output.Ready good h) := by
  induction entries generalizing gro with
  | nil =>
    simpa only [List.forIn_nil] using
      (PrefixEnsures.pure (fun _ _ input => input.1.1) (fun _ _ input => input.1) :
        PrefixEnsures (fun h (_ : World) => (Safe h ∧ gro.Ready good h) ∧
          ∀ entry ∈ ([] : List Entry), good entry h) Safe (pure gro)
          (fun output h _ => Safe h ∧ output.Ready good h))
  | cons entry entries ih =>
    simp only [List.forIn_cons,bind_assoc,pure_bind]
    apply PrefixEnsures.bind
    · apply (remember _ (normalOne_checked good mono Safe callback checked gro entry 1)
        (fun h => ∀ value ∈ entries, good value h)
        (fun history suffix before value member => mono value history suffix (before value member))).consequence
      · intro _ _ input
        exact ⟨⟨input.1,input.2 entry (by simp)⟩,fun value member => input.2 value (by simp [member])⟩
      · intro _ _ _ output; exact output
    · intro output
      exact ih output

theorem flushAll_checked (good : Entry → List E → Prop) (mono : MonotoneWitness good)
    (Safe : List E → Prop) (callback : List Entry → PrefixM E Unit)
    (checked : ∀ entries, PrefixEnsures
      (fun h _ => Safe h ∧ ∀ entry ∈ entries, good entry h) Safe (callback entries)
      (fun _ h _ => Safe h)) (gro : Buffer) :
    PrefixEnsures (fun h _ => Safe h ∧ gro.Ready good h) Safe (flushAllWith callback gro)
      (fun _ h _ => Safe h) := by
  unfold flushAllWith
  apply PrefixEnsures.bind
  · exact (flush_entries_checked good mono Safe callback checked gro.held gro).consequence
      (fun _ _ input => ⟨input,input.2.2⟩) (fun _ _ _ output => output)
  · intro buffer
    apply PrefixEnsures.bind
    · exact (normalList_checked good mono Safe callback checked {buffer with held := []}).consequence
        (fun _ _ input => ⟨input.1,input.2.clearHeld⟩) (fun _ _ _ output => output)
    · intro _
      exact PrefixEnsures.pure (fun _ _ input => input.1) (fun _ _ input => input.1)

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
