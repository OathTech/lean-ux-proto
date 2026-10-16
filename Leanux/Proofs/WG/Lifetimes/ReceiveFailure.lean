import Leanux.Proofs.WG.Lifetimes.CounterAccess

/-! An actual malformed-bitmap error retains the successful keypair lookup.
The premise is the original getter, not an observer history or safety fact. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem counterValidatePrefix_empty_bitmap (kp : KeypairId) (w : WGWorld) (ambient : Ambient)
    (k : Keypair) (h : List LifetimeEvent)
    (hg : ((getKeypair kp).run w).run ambient = .ok ((k, w), ambient))
    (hc : k.receivingCounter = ⟨0, #[]⟩) :
    runStatePrefix (counterValidatePrefix kp 0) w ambient h =
      (.error (.invariant "backtrack[0] beyond the bitmap"),
        h ++ [.keypair (.read kp k.internalId)]) := by
  simp [counterValidatePrefix, runStatePrefix_bind, getKeypairPrefix_run, hg, hc,
    liftWGPrefix, runStatePrefix_lift, WG.orM, branch, branchCmp, invariant, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, StateT.run_bind,
    StateT.run_modify, COUNTER_WINDOW_SIZE, REJECT_AFTER_MESSAGES,
    COUNTER_BITS_TOTAL, BITS_PER_LONG, Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

end Leanux.Proofs.WG.Lifetimes
