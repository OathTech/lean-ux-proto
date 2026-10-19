import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingIterationSource

/-! A failed send iteration retains its exact successful packet/guard prefix
and the matched native send cut on the same ledger. Post-send bookkeeping is
total, so it cannot be used to invent another stopped branch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete

structure IterationStop (context : Context) (skb : SkbId) (rest : List SkbId) (dataSent : Bool)
    (w : World) (history : List CausalJournal.Event) (ledger : Ledger) (debts : List CleanupDebt)
    (reason : Stop) (last : List CausalJournal.Event) where
  packet : RunWitness DataPacket
  world : World
  before : List CausalJournal.Event
  reached : runPrefix (iterationPrefix skb) w history = (.ok (packet,world),before)
  owned : Owned context (.sending (skb :: rest)) before ledger debts world
  complete : Complete before ledger
  packetAt : PacketAt skb packet world
  sendFailure : Failed context skb rest packet world before ledger debts reason last

theorem IterationStop.source_failed
    (cut : IterationStop context skb rest dataSent w history ledger debts reason last) :
    runPrefix (iteration CausalJournal.completionOps context.pid skb dataSent) w history = (.error reason,last) := by
  rw [iteration_factor,runPrefix_bind,cut.reached]
  change runPrefix (afterPacket context.pid skb dataSent cut.packet) cut.world cut.before = _
  rw [afterPacket,runPrefix_bind,cut.sendFailure.source_failed]

theorem iteration_failed
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger)
    (failed : runPrefix (iteration CausalJournal.completionOps context.pid skb dataSent) w history = (.error reason,last)) :
    Nonempty (IterationStop context skb rest dataSent w history ledger debts reason last) := by
  obtain ⟨packet,u,middle,reached,owned,paired,packetAt⟩ := iteration_entry before complete
  rw [iteration_factor,runPrefix_bind,reached] at failed
  change runPrefix (afterPacket context.pid skb dataSent packet) u middle = _ at failed
  rw [afterPacket,runPrefix_bind] at failed
  cases performed : runPrefix (CausalJournal.completionOps.send context.pid skb packet) u middle with
  | mk result after =>
    rw [performed] at failed
    cases result with
    | error stop =>
      cases failed
      exact ⟨⟨packet,u,middle,reached,owned,paired,packetAt,failed_send owned paired packetAt performed⟩⟩
    | ok out =>
      obtain ⟨sent,v⟩ := out
      obtain ⟨value,lastWorld,normal,_⟩ := after_send_total packet dataSent sent v after
      change runPrefix (afterSend packet dataSent sent) v after = _ at failed
      rw [normal] at failed
      cases failed

/-- Recover the original indexed failure from this selected source cut,
keeping its pending or first-terminal ledger rather than rechoosing one. -/
theorem IterationStop.original
    (cut : IterationStop context skb rest dataSent w history ledger debts reason last) :
    Converse.Stopped context skb ledger debts reason last := cut.sendFailure.original

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
