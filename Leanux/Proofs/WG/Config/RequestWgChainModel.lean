import Leanux.Proofs.WG.Config.RequestOrderModel

/-! WG-state adjacency for completed key/peer receipts. Ambient snapshots are intentionally not identified: intervening branch logs change them. Stop safety retains only a completed chain. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder.WgLinks
open Leanux Leanux.WG

inductive Chain : Campaign2.State → List Receipt → Campaign2.State → Prop
  | nil (state) : Chain state [] state
  | cons {state final r rest} (before : r.before.wg=state)
      (tail : Chain r.after.wg rest final) : Chain state (r::rest) final

def NoKey (h : List Receipt) : Prop := ∀r∈h,r.kind≠.keyStage

def Before (h : List Receipt) : Prop := NoKey h ∧ peerReceipts h=[]

def At (h : List Receipt) (state : Campaign2.State) : Prop :=
  ∀r∈h,r.kind=.keyStage→Chain r.after.wg (peerReceipts h) state

def Safe (h : List Receipt) : Prop := NoKey h ∨ ∃state,At h state

def Facts (result : Inspection) : Prop :=
  Safe result.receipts ∧ match result.outcome with
  | .error _=>True
  | .ok (_,final)=>At result.receipts final.wg

end Leanux.Proofs.WG.Config.RequestOrder.WgLinks
