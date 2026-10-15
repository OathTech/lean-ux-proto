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
    Returns (ids.mapM (receivedWithKeypair pid)) (fun w => w.k.wg = some d)
      (fun results w => results = List.replicate ids.length false ∧ w.k.wg = some d) := by
  induction ids with
  | nil =>
    intro w pre
    exact ⟨[], w, rfl, rfl, pre⟩
  | cons id ids ih =>
    intro w pre
    have different := miss id (by simp)
    obtain ⟨ok, middle, headRun, next, device, effect⟩ :=
      receivedWithKeypair_returns_ready pid id d p resident
        (fun matched => False.elim (different matched)) w pre
    have result : ok = false ∧ next = d := by
      simpa only [ConfirmationEffect, different, ite_false] using effect
    obtain ⟨rfl, rfl⟩ := result
    obtain ⟨results, final, tailRun, values, finalDevice⟩ :=
      ih (fun other member => miss other (List.mem_cons_of_mem id member)) middle device
    subst results
    refine ⟨false :: List.replicate ids.length false, final, ?_, rfl, finalDevice⟩
    rw [List.mapM_cons, StateT.run_bind, headRun]
    change ((ids.mapM (receivedWithKeypair pid)) >>= fun values =>
      (pure (false :: values) : M (List Bool))).run middle = _
    rw [StateT.run_bind, tailRun]
    rfl

/-- Decompose a normal original mapM return at its actual first call. -/
theorem confirmation_cons_run (pid : PeerId) (id : KeypairId) (ids : List KeypairId)
    (w out : World) (results : List Bool)
    (run : ((id :: ids).mapM (receivedWithKeypair pid)).run w = .ok (results, out)) :
    ∃ ok middle tail,
      (receivedWithKeypair pid id).run w = .ok (ok, middle) ∧
      (ids.mapM (receivedWithKeypair pid)).run middle = .ok (tail, out) ∧
      results = ok :: tail := by
  rw [List.mapM_cons, StateT.run_bind] at run
  cases headRun : (receivedWithKeypair pid id).run w with
  | error stop => rw [headRun] at run; cases run
  | ok pair =>
    obtain ⟨ok, middle⟩ := pair
    rw [headRun] at run
    change ((ids.mapM (receivedWithKeypair pid)) >>= fun values =>
      (pure (ok :: values) : M (List Bool))).run middle = _ at run
    rw [StateT.run_bind] at run
    cases tailRun : (ids.mapM (receivedWithKeypair pid)).run middle with
    | error stop => rw [tailRun] at run; cases run
    | ok pair =>
      obtain ⟨tail, final⟩ := pair
      rw [tailRun] at run
      change Except.ok (ok :: tail, final) = Except.ok (results, out) at run
      cases run
      exact ⟨ok, middle, tail, rfl, tailRun, rfl⟩

/-- Normal effects of consecutive original calls, without an interleaved next
installation. Stopped executions are not converted to successful results. -/
theorem confirmationSequence_effect (pid : PeerId) (ids : List KeypairId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Ensures (ids.mapM (receivedWithKeypair pid)) (fun w => w.k.wg = some d)
      (fun results w => ∃ final, w.k.wg = some final ∧
        ConfirmationSequenceEffect pid ids d p results final) := by
  induction ids with
  | nil =>
    intro w results out pre run
    change Except.ok ([], w) = Except.ok (results, out) at run
    cases run
    exact ⟨d, pre, Or.inl ⟨rfl, rfl, by simp⟩⟩
  | cons id ids ih =>
    intro w results out pre run
    obtain ⟨ok, middle, tail, headRun, tailRun, rfl⟩ :=
      confirmation_cons_run pid id ids w out results run
    obtain ⟨next, device, effect⟩ :=
      receivedWithKeypair_effect pid id d p resident w ok middle pre headRun
    by_cases matched : p.keypairNext = some id
    · have success : ok = true := by
        have paired : ok = true ∧ RotationRun pid d (confirmationPlan p id) next := by
          simpa only [ConfirmationEffect, matched, ite_true] using effect
        exact paired.1
      subst ok
      obtain ⟨caller, callerResident, empty⟩ :=
        confirmation_true_next_none pid id d next p resident effect
      obtain ⟨values, final, suffixRun, allFalse, finalDevice⟩ :=
        confirmation_mismatches_return_false pid next caller callerResident ids
          (by intro other member; simp [empty]) middle device
      have equality := tailRun.symm.trans suffixRun
      have pair := Except.ok.inj equality
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
      refine ⟨next, finalDevice, Or.inr ?_⟩
      exact ⟨[], id, ids, rfl, by simp, matched, by simp [allFalse], effect,
        caller, callerResident, empty⟩
    · have result : ok = false ∧ next = d := by
        simpa only [ConfirmationEffect, matched, ite_false] using effect
      obtain ⟨rfl, rfl⟩ := result
      obtain ⟨final, finalDevice, rest⟩ := ih middle tail out device tailRun
      exact ⟨final, finalDevice,
        confirmationSequenceEffect_miss pid id ids _ final p tail matched rest⟩

/-- A single conditional old-previous budget suffices for this finite list;
after the first match, all remaining calls take their original mismatch return. -/
theorem confirmationSequence_returns_ready (pid : PeerId) (ids : List KeypairId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (ready : (∃ id ∈ ids, p.keypairNext = some id) → ClearReady d [p.keypairPrevious]) :
    Returns (ids.mapM (receivedWithKeypair pid)) (fun w => w.k.wg = some d)
      (fun results w => ∃ final, w.k.wg = some final ∧
        ConfirmationSequenceEffect pid ids d p results final) := by
  have completes : ∀ w, w.k.wg = some d →
      ∃ results out, (ids.mapM (receivedWithKeypair pid)).run w = .ok (results, out) := by
    induction ids with
    | nil => intro w pre; exact ⟨[], w, rfl⟩
    | cons id ids ih =>
      intro w pre
      obtain ⟨ok, middle, headRun, next, device, effect⟩ :=
        receivedWithKeypair_returns_ready pid id d p resident
          (fun matched => ready ⟨id, by simp, matched⟩) w pre
      by_cases matched : p.keypairNext = some id
      · have success : ok = true := by
          have paired : ok = true ∧ RotationRun pid d (confirmationPlan p id) next := by
            simpa only [ConfirmationEffect, matched, ite_true] using effect
          exact paired.1
        subst ok
        obtain ⟨caller, callerResident, empty⟩ :=
          confirmation_true_next_none pid id d next p resident effect
        obtain ⟨values, final, tailRun, _, _⟩ :=
          confirmation_mismatches_return_false pid next caller callerResident ids
            (by intro other member; simp [empty]) middle device
        refine ⟨true :: values, final, ?_⟩
        rw [List.mapM_cons, StateT.run_bind, headRun]
        change ((ids.mapM (receivedWithKeypair pid)) >>= fun values =>
          (pure (true :: values) : M (List Bool))).run middle = _
        rw [StateT.run_bind, tailRun]
        rfl
      · have result : ok = false ∧ next = d := by
          simpa only [ConfirmationEffect, matched, ite_false] using effect
        obtain ⟨rfl, rfl⟩ := result
        obtain ⟨values, final, tailRun⟩ := ih
          (fun ⟨other, member, hit⟩ => ready ⟨other, List.mem_cons_of_mem id member, hit⟩)
          middle device
        refine ⟨false :: values, final, ?_⟩
        rw [List.mapM_cons, StateT.run_bind, headRun]
        change ((ids.mapM (receivedWithKeypair pid)) >>= fun values =>
          (pure (false :: values) : M (List Bool))).run middle = _
        rw [StateT.run_bind, tailRun]
        rfl
  intro w pre
  obtain ⟨results, out, run⟩ := completes w pre
  exact ⟨results, out, run, confirmationSequence_effect pid ids d p resident w results out pre run⟩

end Leanux.Proofs.WG.Noise
