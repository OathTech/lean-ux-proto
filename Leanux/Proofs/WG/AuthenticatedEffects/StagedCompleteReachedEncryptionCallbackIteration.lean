import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionCallbackPoints
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointInitialized

/-! Committed encryption calls use their actual selected batch and fixed
callback cuts, including the return before its receipt and the fixed native
encryption preparation, key-read and scatter-check points. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCallback
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def iterationPoints (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  fun token w h u middle=>match token with
  | .encrypt item=>Point item w h u middle
  | token=>other token w h u middle

/-- The selected encryption callback derives conservation at every declared
preparation, loop, byte-write and publication cut on its original ledger,
including native peer-release points, without an encryption-child safety premise. -/
noncomputable def encrypt_contract {native inside : Iteration.Points.ChildPoints}
    {Good : List Event → World → Prop}
    (accept : ∀ledger h w,Evidence ledger [] [] h w → Good h w)
    (item : Option (List SkbId)) : Iteration.Points.ChildSourceContract
      (iterationPoints native) (iterationPoints inside) Good (.encrypt item) where
  remainder:=remainder item
  continuation:=fun _ _ _ _ point=>remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,account⟩:=before.1
    exact accept ledger middle u (point.evidence account)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCallback
