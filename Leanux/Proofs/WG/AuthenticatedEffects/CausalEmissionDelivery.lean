import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionPositions
import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryNativeFrames

/-! Delivery certificates preserve every pre-clear occurrence in the same
journal. The local delivery contract requires live append accounting at entry;
it does not infer that invariant from an empty final sent list. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
open Leanux Leanux.WG Leanux.Proofs.Logged

def Checked (pre : List Event) : Event → Prop
  | .delivery sent => ∃ earlier, emitted pre = earlier ++ sent
  | _ => True

def Safe (history : List Event) : Prop :=
  ∀ pre event post, history = pre ++ event :: post → Checked pre event

def Carrier (history : List Event) (w : WGWorld) : Prop :=
  Emissions.Inv history w ∧ Safe history

theorem Safe.empty : Safe [] := by
  intro pre event post position
  have sizes := congrArg List.length position
  simp at sizes

theorem Safe.append (hi : Safe h)
    (checked : ∀ pre event post, suffix = pre ++ event :: post → Checked (h ++ pre) event) :
    Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix hi checked

theorem Safe.emit (hi : Safe h) (checked : Checked h event) : Safe (h ++ [event]) := by
  apply hi.append
  intro pre entry post position
  cases pre with
  | nil => cases position; simpa only [List.append_nil] using checked
  | cons first rest =>
    have sizes := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega

/-- The delivery-entry receipt covers the exact ordered native sent list even
when the following native delivery stops. Normal completion clears that list. -/
theorem deliver : PrefixPreserves (fun h w => Carrier h w.wg) Safe hooks.deliver := by
  change PrefixPreserves (fun h w => Carrier h w.wg) Safe (DeliverySource.observed Event.delivery)
  intro w h hi
  rw [DeliverySource.observed_run]
  have saved : Safe (h ++ [.delivery w.wg.sent]) := hi.2.emit hi.1
  refine ⟨[.delivery w.wg.sent],rfl,saved,?_⟩
  cases run : Env.deliverSent.run w with
  | error stop => trivial
  | ok value =>
    obtain ⟨result,v⟩ := value
    exact ⟨Emissions.Inv.empty (DeliverySource.delivered_empty w v result run),saved⟩

/-- Each pre-delivery position has a distinct append ordinal strictly inside
the receipt prefix preceding this delivery event. -/
theorem Safe.locate (safe : Safe history)
    (position : history = pre ++ Event.delivery sent :: post)
    (index : Nat) (datagram : SentDatagram) (atPosition : sent[index]? = some datagram) :
    Emissions.Occurrence pre ((emitted pre).length - sent.length + index) datagram := by
  obtain ⟨earlier,historyEq⟩ := safe pre (.delivery sent) post position
  have lengths := congrArg List.length historyEq
  simp only [List.length_append] at lengths
  have offset : (emitted pre).length - sent.length = earlier.length := by omega
  apply Emissions.locate
  rw [offset,historyEq,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  exact atPosition

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries
