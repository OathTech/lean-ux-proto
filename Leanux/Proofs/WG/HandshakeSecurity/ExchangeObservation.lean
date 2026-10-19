import Leanux.Proofs.WG.HandshakeSecurity.ExchangeFrames

/-! Receipts are emitted at the completed native operation, before its caller
continues. The failing native callback itself has no invented successful edge;
already completed exchanges remain in a later stopped prefix. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged

def createInitiation (pid : PeerId) : WGPrefix Event (Option (List UInt8)) :=
  receiptWGObserved (liftWGPrefix (WG.createInitiation pid)) (.createInitiation pid)
def consumeInitiation (msg : List UInt8) : WGPrefix Event (Option PeerId) :=
  receiptWGObserved (liftWGPrefix (WG.consumeInitiation msg)) (.consumeInitiation msg)
def createResponse (pid : PeerId) : WGPrefix Event (Option (List UInt8)) :=
  receiptWGObserved (liftWGPrefix (WG.createResponse pid)) (.createResponse pid)
def consumeResponse (msg : List UInt8) : WGPrefix Event (Option PeerId) :=
  receiptWGObserved (liftWGPrefix (WG.consumeResponse msg)) (.consumeResponse msg)
def session (pid : PeerId) : WGPrefix Event Bool :=
  receiptWGObserved (liftWGPrefix (beginSession pid)) (.session pid)

abbrev Preserves (g : WGPrefix Event α) : Prop :=
  StatePrefixPreserves (fun h w _ => StateInv h w) Safe g

theorem receipt_checked (H1 : H1ExchangeEdges) (action : WG.M α)
    (record : WGRunWitness α → Event)
    (before : ∀ r, (record r).before = r.before)
    (after : ∀ r, (record r).after = r.after)
    (valid : ∀ r, r.Valid action → (record r).Valid) :
    Preserves (receiptWGObserved (liftWGPrefix action) record) := by
  intro w a h hi
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix action) record w a h
  rw [runWGPrefix_lift] at equation
  change runStatePrefix (receiptWGObserved (liftWGPrefix action) record) w a h = _ at equation
  unfold runStatePrefix at equation
  rw [equation]
  cases run : (action.run w).run a with
  | error stop => exact ⟨[],by simp,⟨hi.choose,hi.choose_spec.1⟩,trivial⟩
  | ok out =>
    rcases out with ⟨⟨result,v⟩,b⟩
    let r : WGRunWitness α := ⟨result,w,v,a,b⟩
    have checked := append H1 h (record r) (by simpa only [before] using hi) (valid r run)
    have post : StateInv (h ++ [record r]) v := by simpa only [after] using checked
    exact ⟨_,rfl,⟨post.choose,post.choose_spec.1⟩,post⟩

theorem createInitiation_checked (H1 : H1ExchangeEdges) (pid : PeerId) : Preserves (createInitiation pid) :=
  receipt_checked H1 _ _ (fun _ => rfl) (fun _ => rfl) (fun _ h => h)
theorem consumeInitiation_checked (H1 : H1ExchangeEdges) (msg : List UInt8) : Preserves (consumeInitiation msg) :=
  receipt_checked H1 _ _ (fun _ => rfl) (fun _ => rfl) (fun _ h => h)
theorem createResponse_checked (H1 : H1ExchangeEdges) (pid : PeerId) : Preserves (createResponse pid) :=
  receipt_checked H1 _ _ (fun _ => rfl) (fun _ => rfl) (fun _ h => h)
theorem consumeResponse_checked (H1 : H1ExchangeEdges) (msg : List UInt8) : Preserves (consumeResponse msg) :=
  receipt_checked H1 _ _ (fun _ => rfl) (fun _ => rfl) (fun _ h => h)
theorem session_checked (H1 : H1ExchangeEdges) (pid : PeerId) : Preserves (session pid) :=
  receipt_checked H1 _ _ (fun _ => rfl) (fun _ => rfl) (fun _ h => h)

theorem createInitiation_erases (pid : PeerId) : ErasesStatePrefix (createInitiation pid) (WG.createInitiation pid) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _
theorem consumeInitiation_erases (msg : List UInt8) : ErasesStatePrefix (consumeInitiation msg) (WG.consumeInitiation msg) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _
theorem createResponse_erases (pid : PeerId) : ErasesStatePrefix (createResponse pid) (WG.createResponse pid) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _
theorem consumeResponse_erases (msg : List UInt8) : ErasesStatePrefix (consumeResponse msg) (WG.consumeResponse msg) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _
theorem session_erases (pid : PeerId) : ErasesStatePrefix (session pid) (beginSession pid) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
