import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSocketPoints

/-! The actual send entry supplies the socket's one packet ticket. The
native append retains its pending receipt until the original emission. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSocket
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal SocketInterior CompleteCarrier
open Staged.Obligations StagedTerminalComplete

theorem Entry.awaiting (entry : Entry context.pid packet w h)
    (before : Owned context (.sending (skb::rest)) h ledger debts w)
    (complete : Complete h ledger) (packetAt : PacketAt skb packet w) :
    Nonempty (Awaiting context skb rest packet entry.peer entry.ipv4
      (h++entry.readEvents.map FirstTerminal.encode) ledger debts
      (familyWorld entry.ipv4 entry.readWorld) entry.result entry.frontWorld entry.events) :=
  from_send_entry before complete packetAt entry.read entry.family entry.front

inductive Evidence (context : Context) (ledger : Ledger) (debts : List CleanupDebt) :
    List CausalJournal.Event → World → Prop where
  | accounted (next : Ledger) (nextDebts : List CleanupDebt) (step : Staged.Obligations.Step ledger next)
      (account : Accounted h next nextDebts (⟨.selected,context.pid,context.items⟩::context.locals) w.wg) :
      Evidence context ledger debts h w
  | pending (point : Awaiting context skb rest packet peer ipv4 h ledger debts entry result frontWorld events) :
      Evidence context ledger debts point.prior (resultWorld frontWorld result)

/-- Security: a socket front retains pending ownership; native egress keeps
the exact receipt owed for that packet; its emission settles the same ticket
once and records the cleanup debt, without repeating the socket operation. -/
theorem Point.evidence
    (before : Owned context (.sending (skb::rest)) h ledger debts w)
    (complete : Complete h ledger) (packetAt : PacketAt skb packet w)
    (point : Point context.pid skb packet w h u middle) : Evidence context ledger debts middle u := by
  cases point with
  | source entry phase=>
    obtain ⟨waiting⟩:=entry.awaiting before complete packetAt
    cases phase with
    | front=>exact .accounted ledger debts (.refl _) ⟨waiting.front_owned.entry,waiting.front_complete⟩
    | result=>exact .pending waiting
    | recorded=>
      let support : FirstTerminal.Support _ _ ledger debts _:=
        ⟨waiting.before.entry.core.physical,waiting.before.entry.core.valid⟩
      have steps:=(support.settle waiting.pending waiting.outcome).1
      exact .accounted _ _ steps ⟨waiting.after.entry,waiting.afterComplete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSocket
