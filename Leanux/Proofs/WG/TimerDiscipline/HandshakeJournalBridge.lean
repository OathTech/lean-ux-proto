import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalModel
import Leanux.Proofs.WG.TimerDiscipline.HookJournalBridge

/-! Native validity witnesses stay behind projected receipt predicates. Validity alone does not certify an arbitrary caller or scheduling context. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

def SessionReceipt.Valid (r : SessionReceipt) : Prop :=
  ∃ g a next inputs, r.before=Campaign2.snapshot g a ∧
    r.after=Campaign2.snapshot next inputs ∧
    ((beginSession r.pid).run g).run a=.ok ((r.begun,next),inputs)
def Event.Valid : Event → Prop
  | .session r => r.Valid
  | .hook r => r.Valid
def ValidHistory (h : List Event) : Prop := ∀e∈h,e.Valid

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
