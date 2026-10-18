import Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption

namespace Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- The observed AEAD occurrences follow a sublist of the selected packet IDs.
This includes receipts retained by a later stopped prefix. -/
def Footprint (ids : List SkbId) (g : PrefixM Receipt α) : Prop :=
  ∀ w h, ∃ suffix, (runPrefix g w h).2 = h ++ suffix ∧
    (suffix.map Receipt.id).Sublist ids

theorem Footprint.pure (x : α) : Footprint [] (pure x) := by
  intro w h
  exact ⟨[], by simp, by simp⟩

theorem Footprint.lift (a : Leanux.M α) : Footprint [] (liftPrefix a) := by
  intro w h
  exact ⟨[], by simp, by simp⟩

theorem Footprint.capture (a : Leanux.M α) : Footprint [] (captureRun a) := by
  intro w h
  refine ⟨[], ?_, by simp⟩
  rw [runPrefix_captureRun]
  cases a.run w <;> simp

theorem Footprint.mono (hg : Footprint xs g) (sub : xs.Sublist ys) : Footprint ys g := by
  intro w h
  obtain ⟨suffix,eq,bound⟩ := hg w h
  exact ⟨suffix,eq,bound.trans sub⟩

theorem Footprint.bind (hg : Footprint xs g) (hf : ∀ x, Footprint ys (f x)) :
    Footprint (xs ++ ys) (g >>= f) := by
  intro w h
  obtain ⟨s,eq,bound⟩ := hg w h
  cases run : runPrefix g w h with
  | mk result hist =>
    simp only [run] at eq
    cases result with
    | error e =>
      refine ⟨s,?_,?_⟩
      · simpa only [runPrefix_bind,run] using eq
      · exact bound.trans (List.sublist_append_left xs ys)
    | ok out =>
      rcases out with ⟨x,v⟩
      obtain ⟨t,eqt,boundt⟩ := hf x v hist
      refine ⟨s ++ t,?_,?_⟩
      · simp only [runPrefix_bind,run]
        rw [eqt,eq,List.append_assoc]
      · simpa only [List.map_append] using bound.append boundt

theorem Footprint.bind_left (hg : Footprint [] g) (hf : ∀ x, Footprint ys (f x)) :
    Footprint ys (g >>= f) := by
  simpa only [List.nil_append] using hg.bind hf

theorem Footprint.bind_right (hg : Footprint xs g) (hf : ∀ x, Footprint [] (f x)) :
    Footprint xs (g >>= f) := by
  simpa only [List.append_nil] using hg.bind hf

theorem Footprint.ite (p : Prop) [Decidable p]
    (ht : p → Footprint xs gt) (he : ¬p → Footprint xs ge) :
    Footprint xs (if p then gt else ge) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ht hp
  · exact he hp

theorem Footprint.forIn (xs : List SkbId) (b : β)
    (g : SkbId → β → PrefixM Receipt (ForInStep β))
    (hg : ∀ x b, Footprint [x] (g x b)) : Footprint xs (forIn xs b g) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using Footprint.pure b
  | cons x xs ih =>
    rw [List.forIn_cons]
    have body := Footprint.bind (hg x b) (ys := xs) (f := fun step =>
      match step with
      | .done b => Pure.pure b
      | .yield b => ForIn.forIn xs b g) (by
        intro step
        cases step with
        | done b => exact (Footprint.pure b).mono (by simp)
        | yield b => exact ih b)
    exact body

theorem crypt_footprint (headId : SkbId) (head : RunWitness DataPacket)
    (id : SkbId) (read : RunWitness DataPacket) : Footprint [id] (crypt headId head id read) := by
  intro w h
  obtain ⟨suffix,eq,len,_⟩ := Encryption.observe_receipts Env.checksumHelp head.value.keypair read.value w
    (h.filterMap (fun r => some r.cipher))
  have out := focusPrefix_suffix (fun r => (⟨headId,head,id,read,r⟩ : Receipt))
    (fun r => some r.cipher) _ w h _ suffix (Prod.ext rfl eq)
  change runPrefix (crypt headId head id read) w h = _ at out
  rw [out]
  refine ⟨suffix.map (fun r => ⟨headId,head,id,read,r⟩),rfl,?_⟩
  cases suffix with
  | nil => simp
  | cons x xs =>
    have empty : xs = [] := by simpa using len
    subst xs
    simp

theorem packet_footprint (headId : SkbId) (head : RunWitness DataPacket)
    (id : SkbId) : Footprint [id] (packet headId head id) := by
  unfold packet
  exact Footprint.bind_left (Footprint.capture _) (fun _ => crypt_footprint _ _ _ _)

macro "footprint_quiet" : tactic => `(tactic| first
  | exact Footprint.lift _
  | exact Footprint.pure _
  | apply Footprint.bind_left
  | apply Footprint.ite
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem afterHead_footprint (first : List SkbId) (headId : SkbId)
    (head : RunWitness DataPacket) : Footprint first (afterHead first headId head) := by
  unfold afterHead
  apply Footprint.bind_right
  · apply Footprint.forIn
    intro id state
    apply Footprint.bind_left (Footprint.lift _)
    intro _
    apply Footprint.bind_right (packet_footprint _ _ _)
    intro encrypted
    repeat' footprint_quiet
  · intro state
    repeat' footprint_quiet

theorem tail_footprint (item : Option (List SkbId)) :
    Footprint (item.getD []) (tail item) := by
  unfold tail
  apply Footprint.bind_left (Footprint.lift _)
  intro _
  cases item with
  | none => exact Footprint.pure _
  | some first =>
    dsimp only
    cases selected : first.head? with
    | none => exact (Footprint.lift _).mono (by simp)
    | some headId =>
      simp only
      apply Footprint.bind_left (Footprint.capture _)
      intro head
      exact afterHead_footprint _ _ _

/-- A batch containing distinct packet IDs cannot perform AEAD twice for one
packet in this worker selection, even when a later native operation stops. -/
theorem tail_occurrences (item : Option (List SkbId)) (w : World)
    (unique : (item.getD []).Nodup) :
    ((runPrefix (tail item) w []).2.map Receipt.id).Nodup ∧
      ((runPrefix (tail item) w []).2.map Receipt.id).Sublist (item.getD []) := by
  obtain ⟨suffix,eq,sub⟩ := tail_footprint item w []
  simp only [List.nil_append] at eq
  rw [eq]
  exact ⟨unique.sublist sub,sub⟩

end Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption
