import Leanux.Proofs.WG.Campaign2.View

/-! Projected invocation receipts for the eight timer hooks. A stopped outcome has no successor snapshot. The handshake-completion site is retained as input data; caller legitimacy is a separate source obligation. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal
open Leanux Leanux.WG

inductive Hook where
  | handshakeInitiated | dataSent | dataReceived
  | authenticatedSent | authenticatedReceived
  | handshakeComplete (site : HiddenSite)
  | sessionDerived | traversal

structure Receipt where
  hook : Hook
  pid : PeerId
  before : Campaign2.Snapshot
  outcome : Campaign2.Outcome Unit

end Leanux.Proofs.WG.TimerDiscipline.HookJournal
