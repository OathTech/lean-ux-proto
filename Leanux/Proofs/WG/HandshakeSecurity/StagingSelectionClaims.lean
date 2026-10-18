import Leanux.Proofs.WG.HandshakeSecurity.StagingSelectionSource

namespace Leanux.Proofs.WG.HandshakeSecurity.StagingSelection
open Leanux Leanux.WG Leanux.Proofs.Logged
open KeyTimes

def Good (h : List Receipt) : Prop := ∀ a ∈ h, a.Valid

variable {S T : Type}

def keep (C : Prop) (h : List Receipt) (_ : S) : Prop := Good h ∧ C

theorem lift_keep (a : StateT S (Except Stop) α) (C : Prop) :
    PrefixEnsures (keep C) Good (liftPrefix a) (fun _ => keep C) :=
  PrefixEnsures.lift a (fun _ _ hi => hi.1) (fun _ _ _ _ hi _ => hi)

theorem lift_forget (a : StateT S (Except Stop) α) (C : Prop) :
    PrefixEnsures (keep C) Good (liftPrefix a) (fun _ => keep True) :=
  (lift_keep a C).consequence (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, trivial⟩)

theorem pure_forget (x : α) (C : Prop) :
    PrefixEnsures (keep (S := S) C) Good (pure x) (fun _ => keep True) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => ⟨hi.1, trivial⟩)

theorem lift_state_keep (a : StateT S (StateT T (Except Stop)) α) (C : Prop) :
    StatePrefixEnsures (fun h s _ => keep C h s) Good (liftStatePrefix a)
      (fun _ h s _ => keep C h s) :=
  fun s => lift_keep (a.run s) C

theorem lift_state_forget (a : StateT S (StateT T (Except Stop)) α) (C : Prop) :
    StatePrefixEnsures (fun h s _ => keep C h s) Good (liftStatePrefix a)
      (fun _ h s _ => keep True h s) :=
  fun s => lift_forget (a.run s) C

theorem pure_state_forget (x : α) (C : Prop) :
    StatePrefixEnsures (fun h (s : S) (_ : T) => keep C h s) Good (pure x)
      (fun _ h s _ => keep True h s) :=
  fun s => pure_forget (x, s) C

theorem capture_wg_keep (a : WG.M α) (C : Prop) :
    StatePrefixEnsures (fun h s _ => keep C h s) Good (captureWGRun a)
      (fun r h s _ => keep (C ∧ r.Valid a) h s) := by
  apply StatePrefixEnsures.captureWGRun _ (fun _ _ _ hi => hi.1)
  intro h w ambient x v ambient' hi hr
  exact ⟨hi.1, hi.2, hr⟩

theorem branch_state_keep (d : Decision) (b : Bool) (C : Prop) :
    StatePrefixEnsures (fun h s _ => keep C h s) Good (liftWGPrefix (branch d b))
      (fun x h s _ => keep (C ∧ x = b) h s) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w ambient x v ambient' hi hr
  cases hr
  exact ⟨hi.1, hi.2, rfl⟩

theorem comparison_state_keep (d : Decision) (b : Bool) (left right : Int) (C : Prop) :
    StatePrefixEnsures (fun h s _ => keep C h s) Good (liftWGPrefix (branchCmp d b left right))
      (fun x h s _ => keep (C ∧ x = b) h s) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w ambient x v ambient' hi hr
  cases hr
  exact ⟨hi.1, hi.2, rfl⟩

theorem emit_valid (a : Receipt) (C : Prop) (hv : C → a.Valid) :
    PrefixEnsures (keep (S := S) C) Good (emitPrefix a) (fun _ => keep True) := by
  intro w h hi
  have good : Good (h ++ [a]) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hi.1 e he
    · have : e = a := by simpa using he
      subst e
      exact hv hi.2
  exact ⟨[a], by simp, by simpa using good, by simpa [keep] using good⟩

theorem emit_state_valid (a : Receipt) (C : Prop) (hv : C → a.Valid) :
    StatePrefixEnsures (fun h (s : S) (_ : T) => keep C h s) Good (emitStatePrefix a)
      (fun _ h s _ => keep True h s) := by
  intro s t h hi
  exact emit_valid (S := T) a C hv t h hi

theorem afterSelection_safe (pid : PeerId) (peerRead : WGRunWitness Peer)
    (loanRead : WGRunWitness (Option KeypairId))
    (peerValid : peerRead.Valid (getPeer pid))
    (loanValid : loanRead.Valid (keypairGet peerRead.value.keypairCurrent)) :
    StatePrefixEnsures (fun h s _ => keep True h s) Good
      (afterSelection pid peerRead loanRead) (fun _ h s _ => keep True h s) := by
  unfold afterSelection
  apply StatePrefixEnsures.bind (lift_state_keep _ True)
  intro missing
  split
  · exact lift_state_forget _ _
  · cases selected : loanRead.value with
    | none => exact lift_state_forget _ _
    | some id =>
      apply StatePrefixEnsures.bind (capture_wg_keep _ True)
      intro keyRead
      apply StatePrefixEnsures.bind (branch_state_keep _ _ _)
      intro invalid
      cases invalid with
      | true => exact lift_state_forget _ _
      | false =>
        apply StatePrefixEnsures.bind (capture_wg_keep _ _)
        intro clockRead
        apply StatePrefixEnsures.bind (comparison_state_keep _ _ _ _ _)
        intro expired
        cases expired with
        | true => exact lift_state_forget _ _
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          apply StatePrefixEnsures.consequence
            (P := fun h s _ => keep (gateFacts id keyRead clockRead ∧ batchBounds pid id []) h s)
            (Q := fun _ h s _ => keep True h s)
          · apply StatePrefixEnsures.bind (Q := fun acc : Option Unit × List DataPacket =>
                fun h s _ => keep (gateFacts id keyRead clockRead ∧ batchBounds pid id acc.2) h s)
            · apply StatePrefixEnsures.forInInvariant peerRead.value.staged (none, []) _
                (fun acc : Option Unit × List DataPacket =>
                  fun h s _ => keep (gateFacts id keyRead clockRead ∧ batchBounds pid id acc.2) h s) Good
                (fun _ _ _ _ hi => hi.1)
              intro pkt acc
              apply StatePrefixEnsures.bind (lift_state_keep _ _)
              intro _
              apply StatePrefixEnsures.bind (lift_state_keep _ _)
              intro ds
              apply StatePrefixEnsures.bind (lift_state_keep _ _)
              intro fresh
              apply StatePrefixEnsures.bind (lift_state_keep _ _)
              intro _
              apply StatePrefixEnsures.bind (comparison_state_keep _ _ _ _ _)
              intro rejected
              cases rejected with
              | true =>
                apply StatePrefixEnsures.bind (lift_state_keep _ _)
                intro result
                apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1)
                intro h w ambient hi
                exact ⟨hi.1, hi.2.1⟩
              | false =>
                apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1)
                intro h w ambient hi
                refine ⟨hi.1, hi.2.1.1, ?_⟩
                intro q hq
                rcases List.mem_append.mp hq with old | new
                · exact hi.2.1.2 q old
                · have he : q = DataPacket.mk pid id fresh.sendingCounter pkt ds .uncrypted [] := by simpa using new
                  subst q
                  refine ⟨rfl, rfl, ?_⟩
                  have hn : ¬ fresh.sendingCounter ≥ REJECT_AFTER_MESSAGES := by
                    simpa using hi.2.2.symm
                  change fresh.sendingCounter < REJECT_AFTER_MESSAGES
                  omega
            · intro acc
              rcases acc with ⟨done, ps⟩
              cases done with
              | some result => exact pure_state_forget _ _
              | none =>
                apply StatePrefixEnsures.bind (lift_state_keep _ _)
                intro _
                apply StatePrefixEnsures.bind (lift_state_keep _ _)
                intro fresh
                apply StatePrefixEnsures.bind (lift_state_keep _ _)
                intro _
                apply StatePrefixEnsures.bind (capture_wg_keep _ _)
                intro allocation
                apply StatePrefixEnsures.bind
                · apply emit_state_valid
                  intro hi
                  exact ⟨peerValid, loanValid, selected, hi.1.1.1, hi.1.1.2.1, hi.1.1.2.2.1,
                    hi.1.1.2.2.2, hi.1.2, hi.2⟩
                · intro _
                  exact lift_state_forget _ _
          · intro h w ambient hi
            refine ⟨hi.1, ?_, ?_⟩
            · refine ⟨hi.2.1.1.1.2, ?_, hi.2.1.2, ?_⟩
              · simpa using hi.2.1.1.2.symm
              · simpa using hi.2.2.symm
            · simp [batchBounds]
          · intro _ _ _ _ hi
            exact hi

theorem safe (pid : PeerId) :
    StatePrefixEnsures (fun h s _ => keep True h s) Good
      (observed pid) (fun _ h s _ => keep True h s) := by
  unfold observed
  apply StatePrefixEnsures.bind (capture_wg_keep _ True)
  intro peerRead
  apply StatePrefixEnsures.bind (lift_state_keep _ _)
  intro empty
  split
  · exact pure_state_forget _ _
  · apply StatePrefixEnsures.bind (lift_state_keep _ _)
    intro _
    apply StatePrefixEnsures.bind (capture_wg_keep _ _)
    intro loanRead w a h hi
    exact afterSelection_safe pid peerRead loanRead hi.2.1.2 hi.2.2 w a h ⟨hi.1, trivial⟩

end Leanux.Proofs.WG.HandshakeSecurity.StagingSelection
