import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointLifted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointComposition

/-! The same concrete release family fills the NAPI and committed-iteration
release children. The only codomain premise embeds its derived evidence;
no source-child contract for release is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
open Leanux Leanux.WG Leanux.Proofs.Logged CausalJournal

abbrev Good : History → World → Prop :=
  fun h w=>∃ledger,Evidence ledger [] [] h w.wg

theorem carrier_good (before : Napi.Points.Carrier h w) : Good h w := by
  obtain ⟨ledger,accounted⟩ := before
  exact ⟨ledger,.accounted (AccountAt.initial accounted)⟩

def napiPoints (other : Napi.Points.ChildPoints) : Napi.Points.ChildPoints
  | .release peer,w,h,u,middle => NativePoints peer w h u middle
  | token,w,h,u,middle => other token w h u middle

def iterationPoints (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints
  | .release pid,w,h,u,middle => NativePoints (some pid) w h u middle
  | token,w,h,u,middle => other token w h u middle

noncomputable def napiRelease {G : History → World → Prop}
    (accept : ∀ledger h w,Evidence ledger [] [] h w.wg→G h w)
    (native inside : Napi.Points.ChildPoints) (peer : Option PeerId) :
    Napi.Points.ChildSourceContract (napiPoints native) (napiPoints inside) G (.release peer) where
  remainder:=fun _ _ _ _ point=>continuation point
  continuation:=fun _ _ _ _ point=>continuation_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before
    exact accept ledger middle u (native_evidence accounted point)

noncomputable def iterationRelease {G : History → World → Prop}
    (accept : ∀ledger h w,Evidence ledger [] [] h w.wg→G h w)
    (native inside : Iteration.Points.ChildPoints) (pid : PeerId) :
    Iteration.Points.ChildSourceContract (iterationPoints native) (iterationPoints inside) G (.release pid) where
  remainder:=fun _ _ _ _ point=>continuation point
  continuation:=fun _ _ _ _ point=>continuation_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before.1
    exact accept ledger middle u (native_evidence accounted point)

/-- Any actual release child point now has a concrete account or a total
pending receipt, with the original caller's exact remaining computation. -/
theorem child_covered (before : Napi.Points.Carrier h w)
    (point : NativePoints peer w h u middle) :
    Good middle u ∧ runPrefix (liftWGObserver (CausalJournal.peerRelease peer)) w h=
      runPrefix (continuation point) u middle := by
  obtain ⟨ledger,accounted⟩ := before
  exact ⟨⟨ledger,native_evidence accounted point⟩,continuation_run point⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
