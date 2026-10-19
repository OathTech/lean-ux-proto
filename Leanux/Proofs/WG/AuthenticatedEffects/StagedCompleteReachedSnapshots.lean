import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCuts

/-! Concrete journal snapshots for the projected packet account. This is
an intentionally partial catalogue: ID-only queue events and ordinary crypted
cleanup lifetime events do not provide a complete WG snapshot. Their ownership
changes still require a source interval certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open HandshakeSecurity.StagedConservation

/-- The world is fixed by this exact recorded event, never an independently
chosen existential state. Initialized occurrence provenance is supplied by the
actual journal execution and its receipt contracts. -/
inductive Snapshot (history : List CausalJournal.Event) (position : Nat) : WGWorld → Prop where
  | taken (receipt : Take.Receipt)
      (occurrence : history[position]? = some (.stagingTaken receipt))
      (valid : receipt.Valid) : Snapshot history position receipt.run.after
  | allocated (packets : List DataPacket) (receipt : WGRunWitness (List SkbId))
      (occurrence : history[position]? = some (.old (.allocated packets receipt)))
      (valid : receipt.Valid (packets.mapM newTxSkb)) : Snapshot history position receipt.after
  | socket (receipt : Completion.SocketReceipt)
      (occurrence : history[position]? = some (.old (.socket receipt)))
      (valid : receipt.Valid) : Snapshot history position receipt.socket.after.wg
  | freed (receipt : Terminal.Receipt)
      (occurrence : history[position]? = some (.terminalDrop receipt))
      (valid : receipt.Valid) : Snapshot history position receipt.run.after.wg

/-- An earlier concrete receipt has the same account projection as the
saved cut. Deriving this equality over silent operations is a local source
frame obligation. It must not erase a queue transfer or packet free. -/
def Cut.Anchored (saved : Cut context) (last : List CausalJournal.Event) : Prop :=
  saved.before.IsPrefix last ∧ ∃ position w,
    Snapshot saved.before position w ∧ StagedEntry.view w = StagedEntry.view saved.world.wg

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
