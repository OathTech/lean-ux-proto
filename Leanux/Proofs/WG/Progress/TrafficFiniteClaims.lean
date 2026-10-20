import Leanux.Proofs.WG.Progress.TrafficFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.TrafficFinite
open Leanux

/-- Injection uses finite deferred workers and preserves every original return and Stop. -/
theorem original_inject_finite (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.inject family port msg tos ll dest) (nativeInject family port msg tos ll dest) := by
  rw [nativeInject_source]
  intro state pre
  rfl

/-- Batch completion uses finite scheduling and send callbacks with the original drain guards. -/
theorem original_afterBatch_finite  :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.afterBatch) (nativeAfterBatch) := by
  rw [nativeAfterBatch_source]
  intro state pre
  rfl

/-- The bounded flood preserves complete deferred outcomes for arbitrary messages and records. -/
theorem original_flood_finite (count port family : Nat) (messages : List (List UInt8)) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.flood count port family messages) (nativeFlood count port family messages) := by
  rw [nativeFlood_source]
  intro state pre
  rfl

/-- Every batch item and its completion suffix use finite callbacks with exact original outcomes. -/
theorem original_batch_finite (items : List Env.BatchItem) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.batch items) (nativeBatch items) := by
  rw [nativeBatch_source]
  intro state pre
  rfl

end Leanux.Proofs.WG.Progress.TrafficFinite
