import Leanux.Proofs.WG.Noise.ConfirmationSequenceEffects
import Leanux.Proofs.WG.Noise.RotationSource

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Leanux.Proofs.WG.Config

/-- The actual all-mismatch calls terminate without any release budget. -/
theorem confirmation_mismatches_return_false (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (ids : List KeypairId)
    (miss : ∀ id ∈ ids, p.keypairNext ≠ some id) :
    Returns (ids.mapM (receivedWithKeypair pid)) (fun w => w.dev = some d)
      (fun results w => results = List.replicate ids.length false ∧ w.dev = some d) := by
  induction ids with
  | nil =>
    intro w ambient pre
    exact ⟨[], w, ambient, rfl, rfl, pre⟩
  | cons id ids ih =>
    intro w ambient pre
    have different := miss id (by simp)
    obtain ⟨ok, middle, middleAmbient, headRun, next, device, effect⟩ :=
      receivedWithKeypair_returns_ready pid id d p resident
        (fun matched => False.elim (different matched)) w ambient pre
    have result : ok = false ∧ next = d := by
      simpa only [ConfirmationEffect, different, ite_false] using effect
    obtain ⟨rfl, rfl⟩ := result
    obtain ⟨results, final, after, tailRun, values, finalDevice⟩ :=
      ih (fun other member => miss other (List.mem_cons_of_mem id member)) middle middleAmbient device
    subst results
    refine ⟨false :: List.replicate ids.length false, final, after, ?_, rfl, finalDevice⟩
    rw [List.mapM_cons]
    change (((receivedWithKeypair pid id).run w).run ambient >>= fun ((ok, g), a) =>
      (((ids.mapM (receivedWithKeypair pid)).run g).run a >>= fun ((values, g'), a') =>
        Except.ok ((ok :: values, g'), a'))) = _
    rw [headRun]
    change (((ids.mapM (receivedWithKeypair pid)).run middle).run middleAmbient >>=
      fun ((values, g), a) => Except.ok ((false :: values, g), a)) = _
    rw [tailRun]
    rfl

/-- Decompose a normal original mapM return at its actual first call. -/
theorem confirmation_cons_run (pid : PeerId) (id : KeypairId) (ids : List KeypairId)
    (w out : WGWorld) (ambient after : Ambient) (results : List Bool)
    (run : (((id :: ids).mapM (receivedWithKeypair pid)).run w).run ambient =
      .ok ((results, out), after)) :
    ∃ ok middle middleAmbient tail,
      ((receivedWithKeypair pid id).run w).run ambient = .ok ((ok, middle), middleAmbient) ∧
      ((ids.mapM (receivedWithKeypair pid)).run middle).run middleAmbient = .ok ((tail, out), after) ∧
      results = ok :: tail := by
  rw [List.mapM_cons] at run
  change (((receivedWithKeypair pid id).run w).run ambient >>= fun ((ok, g), a) =>
    (((ids.mapM (receivedWithKeypair pid)).run g).run a >>= fun ((values, g'), a') =>
      Except.ok ((ok :: values, g'), a'))) = _ at run
  cases headRun : ((receivedWithKeypair pid id).run w).run ambient with
  | error stop => rw [headRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨ok, middle⟩, middleAmbient⟩ := pair
    rw [headRun] at run
    change (((ids.mapM (receivedWithKeypair pid)).run middle).run middleAmbient >>=
      fun ((values, g), a) => Except.ok ((ok :: values, g), a)) = _ at run
    cases tailRun : ((ids.mapM (receivedWithKeypair pid)).run middle).run middleAmbient with
    | error stop => rw [tailRun] at run; cases run
    | ok pair =>
      obtain ⟨⟨tail, final⟩, finalAmbient⟩ := pair
      rw [tailRun] at run
      change Except.ok ((ok :: tail, final), finalAmbient) = Except.ok ((results, out), after) at run
      cases run
      exact ⟨ok, middle, middleAmbient, tail, rfl, tailRun, rfl⟩

/-- Normal effects of consecutive original calls, without an interleaved next
installation. Stopped executions are not converted to successful results. -/
theorem confirmationSequence_effect (pid : PeerId) (ids : List KeypairId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Ensures (ids.mapM (receivedWithKeypair pid)) (fun w => w.dev = some d)
      (fun results w => ∃ final, w.dev = some final ∧
        ConfirmationSequenceEffect pid ids d p results final) := by
  induction ids with
  | nil =>
    intro w ambient results out after pre run
    change Except.ok (([], w), ambient) = Except.ok ((results, out), after) at run
    cases run
    exact ⟨d, pre, Or.inl ⟨rfl, rfl, by simp⟩⟩
  | cons id ids ih =>
    intro w ambient results out after pre run
    obtain ⟨ok, middle, middleAmbient, tail, headRun, tailRun, rfl⟩ :=
      confirmation_cons_run pid id ids w out ambient after results run
    obtain ⟨next, device, effect⟩ :=
      receivedWithKeypair_effect pid id d p resident w ambient ok middle middleAmbient pre headRun
    by_cases matched : p.keypairNext = some id
    · have success : ok = true := by
        have paired : ok = true ∧ RotationRun pid d (confirmationPlan p id) next := by
          simpa only [ConfirmationEffect, matched, ite_true] using effect
        exact paired.1
      subst ok
      obtain ⟨caller, callerResident, empty⟩ :=
        confirmation_true_next_none pid id d next p resident effect
      obtain ⟨values, final, finalAmbient, suffixRun, allFalse, finalDevice⟩ :=
        confirmation_mismatches_return_false pid next caller callerResident ids
          (by intro other member; simp [empty]) middle middleAmbient device
      have equality := tailRun.symm.trans suffixRun
      have pair := Except.ok.inj equality
      have stateEquality := (Prod.mk.inj pair).1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj stateEquality
      refine ⟨next, finalDevice, Or.inr ?_⟩
      exact ⟨[], id, ids, rfl, by simp, matched, by simp [allFalse], effect,
        caller, callerResident, empty⟩
    · have result : ok = false ∧ next = d := by
        simpa only [ConfirmationEffect, matched, ite_false] using effect
      obtain ⟨rfl, rfl⟩ := result
      obtain ⟨final, finalDevice, rest⟩ := ih middle middleAmbient tail out after device tailRun
      exact ⟨final, finalDevice,
        confirmationSequenceEffect_miss pid id ids _ final p tail matched rest⟩

/-- A single conditional old-previous budget suffices for this finite list;
after the first match, all remaining calls take their original mismatch return. -/
theorem confirmationSequence_returns_ready (pid : PeerId) (ids : List KeypairId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (ready : (∃ id ∈ ids, p.keypairNext = some id) → ClearReady d [p.keypairPrevious]) :
    Returns (ids.mapM (receivedWithKeypair pid)) (fun w => w.dev = some d)
      (fun results w => ∃ final, w.dev = some final ∧
        ConfirmationSequenceEffect pid ids d p results final) := by
  have completes : ∀ w ambient, w.dev = some d →
      ∃ results out after, ((ids.mapM (receivedWithKeypair pid)).run w).run ambient =
        .ok ((results, out), after) := by
    induction ids with
    | nil => intro w ambient pre; exact ⟨[], w, ambient, rfl⟩
    | cons id ids ih =>
      intro w ambient pre
      obtain ⟨ok, middle, middleAmbient, headRun, next, device, effect⟩ :=
        receivedWithKeypair_returns_ready pid id d p resident
          (fun matched => ready ⟨id, by simp, matched⟩) w ambient pre
      by_cases matched : p.keypairNext = some id
      · have success : ok = true := by
          have paired : ok = true ∧ RotationRun pid d (confirmationPlan p id) next := by
            simpa only [ConfirmationEffect, matched, ite_true] using effect
          exact paired.1
        subst ok
        obtain ⟨caller, callerResident, empty⟩ :=
          confirmation_true_next_none pid id d next p resident effect
        obtain ⟨values, final, after, tailRun, _, _⟩ :=
          confirmation_mismatches_return_false pid next caller callerResident ids
            (by intro other member; simp [empty]) middle middleAmbient device
        refine ⟨true :: values, final, after, ?_⟩
        rw [List.mapM_cons]
        change (((receivedWithKeypair pid id).run w).run ambient >>= fun ((ok, g), a) =>
          (((ids.mapM (receivedWithKeypair pid)).run g).run a >>= fun ((values, g'), a') =>
            Except.ok ((ok :: values, g'), a'))) = _
        rw [headRun]
        change (((ids.mapM (receivedWithKeypair pid)).run middle).run middleAmbient >>=
          fun ((values, g), a) => Except.ok ((true :: values, g), a)) = _
        rw [tailRun]
        rfl
      · have result : ok = false ∧ next = d := by
          simpa only [ConfirmationEffect, matched, ite_false] using effect
        obtain ⟨rfl, rfl⟩ := result
        obtain ⟨values, final, after, tailRun⟩ := ih
          (fun ⟨other, member, hit⟩ => ready ⟨other, List.mem_cons_of_mem id member, hit⟩)
          middle middleAmbient device
        refine ⟨false :: values, final, after, ?_⟩
        rw [List.mapM_cons]
        change (((receivedWithKeypair pid id).run w).run ambient >>= fun ((ok, g), a) =>
          (((ids.mapM (receivedWithKeypair pid)).run g).run a >>= fun ((values, g'), a') =>
            Except.ok ((ok :: values, g'), a'))) = _
        rw [headRun]
        change (((ids.mapM (receivedWithKeypair pid)).run middle).run middleAmbient >>=
          fun ((values, g), a) => Except.ok ((false :: values, g), a)) = _
        rw [tailRun]
        rfl
  intro w ambient pre
  obtain ⟨results, out, after, run⟩ := completes w ambient pre
  exact ⟨results, out, after, run,
    confirmationSequence_effect pid ids d p resident w ambient results out after pre run⟩

end Leanux.Proofs.WG.Noise
