import Leanux.Proofs.WG.TimerDiscipline.HookJournalModel
/-! Projected receive-hook inspection data. The four hook names specify caller scope; they do not establish cryptographic authentication. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.ReceiveHookJournal
open Leanux Leanux.WG HookJournal
def AllowedHook (hook : Hook) : Prop :=
  hook = .handshakeComplete .walltimeLastHandshakeData ∨
  hook = .authenticatedReceived ∨ hook = .traversal ∨ hook = .dataReceived
def Scoped (pid : PeerId) (history : List Receipt) : Prop :=
  ∀ r ∈ history, r.pid = pid ∧ AllowedHook r.hook

structure Inspection where
  outcome : Campaign2.Outcome (Option (List UInt8))
  receipts : List Receipt

end Leanux.Proofs.WG.TimerDiscipline.ReceiveHookJournal
