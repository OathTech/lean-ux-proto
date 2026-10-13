import Leanux.Proofs.WG.Lifetimes.CounterAccess

/-! An actual malformed-bitmap error retains the successful keypair lookup.
The premise is the original getter, not an observer history or safety fact. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem counterValidatePrefix_empty_bitmap (kp : KeypairId) (w : World)
    (k : Keypair) (h : List LifetimeEvent)
    (hg : (getKeypair kp).run w = .ok (k, w))
    (hc : k.receivingCounter = ⟨0, #[]⟩) :
    runPrefix (counterValidatePrefix kp 0) w h =
      (.error (.invariant "backtrack[0] beyond the bitmap"),
        h ++ [.keypair (.read kp k.internalId)]) := by
  simp [counterValidatePrefix, runPrefix_bind, getKeypairPrefix_run, hg, hc,
    runPrefix_lift, WG.orM, branch, branchCmp, invariant, StateT.run_bind,
    StateT.run_modify, COUNTER_WINDOW_SIZE, REJECT_AFTER_MESSAGES,
    COUNTER_BITS_TOTAL, BITS_PER_LONG, Std.Legacy.Range.forIn_eq_forIn_range']
  decide

end Leanux.Proofs.WG.Lifetimes
