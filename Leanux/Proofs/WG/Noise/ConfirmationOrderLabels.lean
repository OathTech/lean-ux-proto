import Leanux.Proofs.WG.Noise.ConfirmationOrderClaims
import Leanux.Proofs.WG.Noise.ConfirmationLabelSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConfirmationOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes ConsumeConfirmation

/-- The label and record use the same actual inner confirmation and entry stamp. -/
theorem matches_label {i n : Nat} {id : SkbId} {stamp : PacketStamp}
    {r : RxDisposition.ConsumeReceipt} {q : Record}
    (matched : Matches i n id stamp r q) :
    CounterConsume.receiptLabel r =
      if q.observation.confirmed then some q.internalId else none := by
  obtain ⟨valid,c,allocation,source,key,rfl⟩ := matched
  have cv : (projects r c).Valid := ⟨r,c,rfl,valid,source⟩
  have label := input_label_actual (projects r c) cv
  have resident :
      projectedStampAt (projects r c).entry (projects r c).packet.keypair = some allocation := key
  rw [resident] at label
  exact label

/-- Extracting labels directly from the journal retains exactly the successful
records, including their order and multiplicity. -/
theorem Ordered.labels {i : Nat} {es : List RxHistory.Event} {qs : List Record}
    (ordered : Ordered i es qs) :
    CounterConsume.confirmationLabels es = successful qs := by
  induction ordered with
  | nil => rfl
  | @cons i e es out qs matched tail ih =>
    cases e with
    | consumed n id stamp r =>
      obtain ⟨q,rfl,hm⟩ := matched
      simp only [CounterConsume.confirmationLabels,List.filterMap_cons,
        CounterConsume.eventLabel,matches_label hm,Option.toList_some,
        List.singleton_append,successful,List.filterMap_cons]
      change es.filterMap CounterConsume.eventLabel =
        qs.filterMap (fun q => if q.observation.confirmed then some q.internalId else none) at ih
      rw [ih]
    | _ =>
      rw [matched]
      exact ih

/-- The initialized extractor succeeds and returns the data-only labels of the
actual committed event prefix, including when the outer trace later Stops. -/
theorem initialized_confirmationIds_labels (trace : Runner.Trace) (placeholders : Bool) :
    confirmationIds trace placeholders =
      .ok (CounterConsume.confirmationLabels (history trace placeholders)) := by
  obtain ⟨qs,_,ids,ordered⟩ := initialized_ordered trace placeholders
  rw [ordered.labels]
  exact ids

end Leanux.Proofs.WG.Noise.ConfirmationOrder
