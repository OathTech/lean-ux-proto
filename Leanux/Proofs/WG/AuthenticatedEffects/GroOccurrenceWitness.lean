import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames

/-! A buffered packet retains its own occurrence witness through later
callback histories. Witnesses are deliberately supplied by the successful
poll branch; GRO does not infer authentication from packet bytes or tags. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
open Leanux Leanux.WG Leanux.Proofs.Logged

def Buffer.Ready (good : Entry → List E → Prop) (gro : Buffer) (history : List E) : Prop :=
  (∀ entry ∈ gro.rxList, good entry history) ∧ (∀ entry ∈ gro.held, good entry history)

def MonotoneWitness (good : Entry → List E → Prop) : Prop :=
  ∀ entry history suffix, good entry history → good entry (history ++ suffix)

theorem Buffer.Ready.append {good : Entry → List E → Prop} (mono : MonotoneWitness good)
    {gro : Buffer} {history : List E} (ready : gro.Ready good history) (suffix : List E) :
    gro.Ready good (history ++ suffix) :=
  ⟨fun entry member => mono entry history suffix (ready.1 entry member),
   fun entry member => mono entry history suffix (ready.2 entry member)⟩

theorem Buffer.Ready.empty (good : Entry → List E → Prop) (history : List E) :
    ({} : Buffer).Ready good history := by simp [Buffer.Ready]

theorem Buffer.Ready.normal {good : Entry → List E → Prop} {gro : Buffer} {history : List E}
    (ready : gro.Ready good history) {entry : Entry} (valid : good entry history) (segs : Nat) :
    ({gro with rxList := gro.rxList ++ [entry], rxCount := gro.rxCount + segs} : Buffer).Ready good history := by
  refine ⟨?_,ready.2⟩
  intro value member
  rcases List.mem_append.mp member with old | added
  · exact ready.1 value old
  · have equal : value = entry := by simpa using added
    simpa only [equal] using valid

theorem Buffer.Ready.clearNormal {good : Entry → List E → Prop} {gro : Buffer} {history : List E}
    (ready : gro.Ready good history) :
    ({gro with rxList := [], rxCount := 0} : Buffer).Ready good history :=
  ⟨fun _ member => False.elim (List.not_mem_nil member),ready.2⟩

theorem Buffer.Ready.clearHeld {good : Entry → List E → Prop} {gro : Buffer} {history : List E}
    (ready : gro.Ready good history) : ({gro with held := []} : Buffer).Ready good history :=
  ⟨ready.1,fun _ member => False.elim (List.not_mem_nil member)⟩

theorem Buffer.Ready.hold {good : Entry → List E → Prop} {gro : Buffer} {history : List E}
    (ready : gro.Ready good history) {entry : Entry} (valid : good entry history) :
    ({gro with held := [entry]} : Buffer).Ready good history := by
  refine ⟨ready.1,?_⟩
  intro value member
  have equal : value = entry := by simpa using member
  simpa only [equal] using valid

theorem Buffer.Ready.appendHeld {good : Entry → List E → Prop} {gro : Buffer} {history : List E}
    (ready : gro.Ready good history) {entry : Entry} (valid : good entry history) :
    ({gro with held := gro.held ++ [entry]} : Buffer).Ready good history := by
  refine ⟨ready.1,?_⟩
  intro value member
  rcases List.mem_append.mp member with old | added
  · exact ready.2 value old
  · have equal : value = entry := by simpa using added
    simpa only [equal] using valid

theorem remember (body : PrefixM E α) (contract : PrefixEnsures P S body Q)
    (witness : List E → Prop)
    (mono : ∀ history suffix, witness history → witness (history ++ suffix)) :
    PrefixEnsures (fun h w => P h w ∧ witness h) S body
      (fun value h w => Q value h w ∧ witness h) := by
  intro w h input
  obtain ⟨suffix,grown,safe,normal⟩ := contract w h input.1
  have kept : witness (runPrefix body w h).2 := by rw [grown]; exact mono h suffix input.2
  refine ⟨suffix,grown,safe,?_⟩
  cases result : (runPrefix body w h).1 with
  | error _ => trivial
  | ok output => exact ⟨by simpa only [result] using normal,kept⟩

theorem normalList_checked (good : Entry → List E → Prop) (mono : MonotoneWitness good)
    (Safe : List E → Prop) (callback : List Entry → PrefixM E Unit)
    (checked : ∀ entries, PrefixEnsures
      (fun h _ => Safe h ∧ ∀ entry ∈ entries, good entry h) Safe (callback entries)
      (fun _ h _ => Safe h)) (gro : Buffer) :
    PrefixEnsures (fun h _ => Safe h ∧ gro.Ready good h) Safe (normalListWith callback gro)
      (fun output h _ => Safe h ∧ output.Ready good h) := by
  unfold normalListWith
  apply PrefixEnsures.ite
  · intro _
    exact PrefixEnsures.pure (fun _ _ input => input.1) (fun _ _ input => input)
  · intro _
    have call : PrefixEnsures (fun h _ => Safe h ∧ gro.Ready good h) Safe (callback gro.rxList)
        (fun _ h _ => Safe h ∧ gro.Ready good h) :=
      (remember _ (checked gro.rxList) (gro.Ready good)
        (fun _ suffix ready => ready.append mono suffix)).consequence
        (fun _ _ input => ⟨⟨input.1,input.2.1⟩,input.2⟩) (fun _ _ _ output => output)
    apply PrefixEnsures.bind call
    intro _
    exact PrefixEnsures.pure (fun _ _ input => input.1)
      (fun _ _ input => ⟨input.1,input.2.clearNormal⟩)

theorem normalOne_checked (good : Entry → List E → Prop) (mono : MonotoneWitness good)
    (Safe : List E → Prop) (callback : List Entry → PrefixM E Unit)
    (checked : ∀ entries, PrefixEnsures
      (fun h _ => Safe h ∧ ∀ entry ∈ entries, good entry h) Safe (callback entries)
      (fun _ h _ => Safe h)) (gro : Buffer) (entry : Entry) (segs : Nat) :
    PrefixEnsures (fun h _ => (Safe h ∧ gro.Ready good h) ∧ good entry h) Safe
      (normalOneWith callback gro entry segs)
      (fun output h _ => Safe h ∧ output.Ready good h) := by
  unfold normalOneWith
  dsimp only
  apply PrefixEnsures.ite
  · intro _
    exact (normalList_checked good mono Safe callback checked _).consequence
      (fun _ _ input => ⟨input.1.1,input.1.2.normal input.2 segs⟩) (fun _ _ _ output => output)
  · intro _
    exact PrefixEnsures.pure (fun _ _ input => input.1.1)
      (fun _ _ input => ⟨input.1.1,input.1.2.normal input.2 segs⟩)

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
