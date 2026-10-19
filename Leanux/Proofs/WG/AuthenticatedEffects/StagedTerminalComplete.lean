import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalProvenanceOrder

/-! Receipt-to-terminal coverage is separate from terminal provenance. Each
actual data socket call or named drop demands the exact number of fixed
terminal tickets at its own full-journal position. This definition alone is
not an initialized claim; native source cuts must establish its transport. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal StagedProvenance

structure Demand where
  outcome : Staged.Obligations.Terminal
  count : Nat

def stagedLength (w : WGWorld) (pid : PeerId) : Nat :=
  ((Staged.stagedAt w pid).map (fun pair => pair.2.length)).getD 0

def endpointFamily (w : WGWorld) (pid : PeerId) : Nat :=
  ((w.dev.bind fun d => d.peers[pid]?).bind (·.endpoint)).map (·.family) |>.getD 0

/-- Socket errno is still the first terminal. A supported-family outer
false result is only a report of that earlier socket result; unsupported
family is the sole outer result that supplies a new terminal. -/
def demand (position : Nat) : Event → Option Demand
  | .old (.socket r) => some ⟨.socket position (r.socket.value == 0),1⟩
  | .terminalDrop r => some ⟨.disposed position r.reason,1⟩
  | .stagedDisposal (.overflow pid r) =>
      some ⟨.counted position .overflow,stagedLength r.before pid - stagedLength r.after pid⟩
  | .stagedDisposal (.purge pid r) => some ⟨.counted position .purge,stagedLength r.before pid⟩
  | .stagedDisposal (.release _ r) =>
      r.value.map fun pair => ⟨.counted position .finalRelease,pair.2.staged.length⟩
  | .sendResult r =>
      let family := endpointFamily r.run.before.wg r.pid
      if family = AF_INET ∨ family = AF_INET6 then none else some ⟨.sendRefused position,1⟩
  | _ => none

noncomputable def tickets (outcome : Staged.Obligations.Terminal) (ledger : Ledger) : List Ticket := by
  classical
  exact ledger.filterMap fun entry => match entry.2 with
    | .pending _ => none
    | .terminal actual => if actual = outcome then some entry.1 else none

def Satisfied (position : Nat) (event : Event) (ledger : Ledger) : Prop :=
  ∀ requested, demand position event = some requested → (tickets requested.outcome ledger).length = requested.count

def Scan (offset : Nat) (history : List Event) (ledger : Ledger) : Prop :=
  match history with
  | [] => True
  | event :: rest => Satisfied offset event ledger ∧ Scan (offset+1) rest ledger

def Complete (history : List Event) (ledger : Ledger) : Prop := Scan 0 history ledger

/-- Quiet means no receipt requiring a terminal, not merely no new birth. -/
def Quiet (event : Event) : Prop := ∀ position, demand position event = none

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
