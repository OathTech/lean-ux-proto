import Leanux.Proofs.WG.Index.SessionInvariantEffects
import Leanux.Proofs.WG.Keypairs.Affiliation
import Leanux.Proofs.WG.Index.SessionSequenceSource
import Leanux.Proofs.WG.Index.OwnerCoherenceSessionClaims
import Leanux.Proofs.WG.Index.TablePreservationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- The actual call preserves the combined session invariant. Its real first
read supplies caller residency; affiliation supplies rotation/allocation
freshness. Normal false results and all original Stops remain possible. -/
theorem beginSession_sessionIndexSafe (pid : PeerId) :
    Campaign2.Ensures (beginSession pid) View.SessionIndexSafe
      (fun _ => View.SessionIndexSafe) := by
  intro w ambient result out after pre run
  cases hd : w.dev with
  | none =>
    simp [beginSession, getPeer, getDev, hd, invariant, AmbientM.invariant,
      StateT.run_bind] at run
    change Except.error (Stop.invariant "no WireGuard device in this trace's fixture") =
      Except.ok ((result,out),after) at run
    cases run
  | some d =>
    have initial := pre d hd
    obtain ⟨p, resident⟩ :=
      beginSession_entry_resident pid d w out ambient after result hd run
    have affiliation : Affiliation.Inv w := by
      intro state hs
      have same : Affiliation.state d = state := by
        simpa only [Affiliation.view, hd, Option.map_some, Option.some.injEq] using hs
      exact same ▸ initial.affiliation
    have bounded := affiliation_hashed_bound d initial.affiliation initial.coherent
    have finalAffiliation := (Leanux.Proofs.Framing.hoare_iff_run_ambient _ _ _).mp
      (Affiliation.beginSession_affiliation pid) w ambient result out after affiliation run
    have finalCoherent := beginSession_owner_coherent pid d p resident bounded
      (affiliation_session_fresh d pid p initial.affiliation resident)
      w ambient result out after ⟨hd, fun actual present => by
        have same : actual = d := Option.some.inj (present.symm.trans hd)
        simpa only [same] using initial.coherent⟩ run
    have finalTables := (ensures_iff _ _ _).mpr (beginSession_tables pid)
      w ambient result out after (fun actual present => by
        have same : actual = d := Option.some.inj (present.symm.trans hd)
        subst actual
        exact ⟨initial.indices, initial.owners, bounded⟩) run
    intro final present
    change out.dev = some final at present
    have table := finalTables final present
    refine ⟨?_, table.1, table.2.1, finalCoherent final present⟩
    exact finalAffiliation (Affiliation.state final)
      (by simp [Affiliation.view, present])

/-- An arbitrary finite list of consecutive actual session calls preserves
the same invariant without supplying fresh conditions at intermediate cuts.
This asserts normal-return preservation, not termination or driver closure. -/
theorem sessionCalls_sessionIndexSafe (pids : List PeerId) :
    Campaign2.Ensures (pids.mapM beginSession) View.SessionIndexSafe
      (fun _ => View.SessionIndexSafe) := by
  induction pids with
  | nil =>
    intro w ambient result out after pre run
    change Except.ok (([],w),ambient) = Except.ok ((result,out),after) at run
    cases run
    exact pre
  | cons pid rest ih =>
    intro w ambient result out after pre run
    rw [List.mapM_cons] at run
    change (((beginSession pid).run w).run ambient >>= fun ((value,middle),input) =>
      ((rest.mapM beginSession).run middle).run input >>= fun ((tail,final),remaining) =>
        Except.ok ((value::tail,final),remaining)) = _ at run
    cases headRun : ((beginSession pid).run w).run ambient with
    | error stop => rw [headRun] at run; cases run
    | ok output =>
      obtain ⟨⟨value,middle⟩,input⟩ := output
      have current := beginSession_sessionIndexSafe pid w ambient value middle input pre headRun
      rw [headRun] at run
      change (((rest.mapM beginSession).run middle).run input >>= fun ((tail,final),remaining) =>
        Except.ok ((value::tail,final),remaining)) = _ at run
      cases tailRun : ((rest.mapM beginSession).run middle).run input with
      | error stop => rw [tailRun] at run; cases run
      | ok output =>
        obtain ⟨⟨tail,final⟩,remaining⟩ := output
        rw [tailRun] at run
        cases run
        exact ih middle input tail out after current tailRun

end Leanux.Proofs.WG.Index
