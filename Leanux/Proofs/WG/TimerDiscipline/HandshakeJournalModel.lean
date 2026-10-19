import Leanux.Proofs.WG.TimerDiscipline.HookJournalModel

/-! Projected completed-session and hook-invocation receipts. A successful session is paired with the immediately following derived-hook invocation; the hook may Stop. Counter labels are actual persistent counters, not a global uniqueness assumption. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

structure SessionReceipt where
  pid : PeerId
  before : Campaign2.Snapshot
  begun : Bool
  after : Campaign2.Snapshot
inductive Event where
  | session (receipt : SessionReceipt)
  | hook (receipt : HookJournal.Receipt)
def decodeHook : Event → Option HookJournal.Receipt
  | .session _ => none
  | .hook r => some r
def SessionDerivedLink (s : SessionReceipt) (r : HookJournal.Receipt) : Prop :=
  s.begun=true ∧ r.hook=.sessionDerived ∧ r.pid=s.pid ∧ r.before.wg=s.after.wg ∧
  r.before.wg.keypairCounter=s.before.wg.keypairCounter+1
inductive Paired : List Event → Prop
  | nil : Paired []
  | quiet {h} (r : HookJournal.Receipt) (prior : Paired h)
      (other : r.hook≠.sessionDerived) : Paired (h++[.hook r])
  | refused {h} (s : SessionReceipt) (prior : Paired h)
      (notBegun : s.begun=false) : Paired (h++[.session s])
  | derived {h} (s : SessionReceipt) (r : HookJournal.Receipt) (prior : Paired h)
      (link : SessionDerivedLink s r) : Paired (h++[.session s,.hook r])
def Event.sessionId : Event → Option Nat
  | .session r => if r.begun then some r.after.wg.keypairCounter else none
  | .hook _ => none
def Event.derivedId : Event → Option Nat
  | .session _ => none
  | .hook r => match r.hook with
    | .sessionDerived => some r.before.wg.keypairCounter
    | _ => none
abbrev Inspection (α : Type) := Campaign2.Outcome α × List Event

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
