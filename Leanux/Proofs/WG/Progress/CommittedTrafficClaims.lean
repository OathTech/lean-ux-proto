import Leanux.Proofs.WG.Progress.CommittedTrafficSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Traffic
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

/-! These inspections retain actual scheduler receipts on any outcome.
They do not infer call provenance from arbitrary supplied ValidHistory. -/
def observed {α : Type} (action : PrefixM Receipt α) :
    Leanux.M (Campaign2.Product.Outcome α × List Receipt) := fun entry =>
  let result:=runPrefix action entry []
  .ok ((Campaign2.Product.observeResult result.1,result.2),entry)

theorem observed_correct {α : Type} (action : PrefixM Receipt α) (native : Leanux.M α)
    (erase : ErasesPrefix action native)
    (valid : PrefixPreserves (fun h _=>ValidHistory h) ValidHistory action) :
    (do let result←observed action; pure result.1) = Campaign2.Product.inspect native ∧
    Campaign2.Product.Returns (observed action) (fun _=>True)
      (fun result _=>ValidHistory result.2) := by
  constructor
  · funext entry
    change Except.ok (Campaign2.Product.observeResult (runPrefix action entry []).1,entry) =
      Except.ok (Campaign2.Product.observeResult (native.run entry),entry)
    rw [erase entry []]
  · intro entry _
    obtain ⟨_,_,safe,_⟩:=valid entry [] (by intro r member; cases member)
    exact ⟨_,entry,rfl,safe⟩

theorem original_inject_journal (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    (do let result←observed (inject family port msg tos ll dest); pure result.1) =
      Campaign2.Product.inspect (Env.inject family port msg tos ll dest) ∧
    Campaign2.Product.Returns (observed (inject family port msg tos ll dest)) (fun _=>True)
      (fun result _=>ValidHistory result.2) :=
  observed_correct _ _ (inject_erases family port msg tos ll dest) (inject_preserves family port msg tos ll dest)

theorem original_afterBatch_journal  :
    (do let result←observed (afterBatch); pure result.1) =
      Campaign2.Product.inspect (Env.afterBatch) ∧
    Campaign2.Product.Returns (observed (afterBatch)) (fun _=>True)
      (fun result _=>ValidHistory result.2) :=
  observed_correct _ _ (afterBatch_erases) (afterBatch_preserves)

theorem original_flood_journal (count port family : Nat) (messages : List (List UInt8)) :
    (do let result←observed (flood count port family messages); pure result.1) =
      Campaign2.Product.inspect (Env.flood count port family messages) ∧
    Campaign2.Product.Returns (observed (flood count port family messages)) (fun _=>True)
      (fun result _=>ValidHistory result.2) :=
  observed_correct _ _ (flood_erases count port family messages) (flood_preserves count port family messages)

theorem original_batchItem_journal (device : Device) (cqes : List Int) (item : Env.BatchItem) :
    (do let result←observed (batchItem device cqes item); pure result.1) =
      Campaign2.Product.inspect (Environment.batchItemSource device cqes item) ∧
    Campaign2.Product.Returns (observed (batchItem device cqes item)) (fun _=>True)
      (fun result _=>ValidHistory result.2) :=
  observed_correct _ _ (batchItem_erases device cqes item) (batchItem_preserves device cqes item)

theorem original_batch_journal (items : List Env.BatchItem) :
    (do let result←observed (batch items); pure result.1) =
      Campaign2.Product.inspect (Env.batch items) ∧
    Campaign2.Product.Returns (observed (batch items)) (fun _=>True)
      (fun result _=>ValidHistory result.2) :=
  observed_correct _ _ (batch_erases items) (batch_preserves items)

theorem original_observe_journal  :
    (do let result←observed (observe); pure result.1) =
      Campaign2.Product.inspect (Env.observe) ∧
    Campaign2.Product.Returns (observed (observe)) (fun _=>True)
      (fun result _=>ValidHistory result.2) :=
  observed_correct _ _ (observe_erases) (observe_preserves)

end Leanux.Proofs.WG.Progress.CommittedRuns.Traffic
