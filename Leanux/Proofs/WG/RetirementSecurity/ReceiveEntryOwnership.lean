import Leanux.Proofs.WG.RetirementSecurity.ReceiveOccurrences

/-! Full native receive-entry ownership contracts and the shared-driver cut.
The incoming allocation witness is campaign 1's source-derived invariant;
queue aliases contribute no extra key reference. Whole Runner transport is
not asserted by these local caller results. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged

namespace ReceiveEntry
abbrev Joint (temporary : Credits.Ledger) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (w : WGWorld) :=
  DriverOwnership.Boundary temporary locals active w ∧ StackOwnership.Allocated w

theorem initial (net bare : Bool) : Joint [] [] [] (Runner.initialWG net bare) :=
  ⟨DriverOwnership.initial net bare,⟨[],Lifetimes.allocation_initial net bare _ rfl⟩⟩

theorem joint (before : Joint temporary locals active w) (msg : List UInt8)
    (src : SkbSource) (a b : Ambient)
    (run : ((wgReceive msg src).run w).run a = .ok (((),v),b)) : Joint temporary locals active v := by
  have keys := (hoare_iff_run_ambient _ _ _).mp (receive msg src)
    w a () v b ⟨before.1.1,before.2⟩ run
  have packets := (hoare_iff_run_ambient _ _ _).mp (ReceiveOccurrences.receive msg src)
    w a () v b before.1.2 run
  exact ⟨⟨keys.1,packets⟩,keys.2⟩

theorem shared {E : Type} (before : Joint temporary locals active w.wg)
    (msg : List UInt8) (src : SkbSource) (h : List E)
    (run : (runPrefix (TransmitSecurity.Driver.receiveEntryObserved msg src) w h).1 = .ok ((),v)) :
    Joint temporary locals active v.wg := by
  change (liftWG (wgReceive msg src)).run w = .ok ((),v) at run
  rw [liftWG_run] at run
  cases native : ((wgReceive msg src).run w.wg).run w.ambient with
  | error e => simp [native,Except.map] at run
  | ok output =>
    obtain ⟨⟨result,g⟩,a⟩ := output
    cases result
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq,true_and] at run
    subst v
    exact joint before msg src w.ambient a native

end ReceiveEntry
end Leanux.Proofs.WG.RetirementSecurity
