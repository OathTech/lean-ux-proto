import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointMutation

/-! A refused creation's labelled free has a source-derived native erase and
fixed pending emissions. The original allocated ticket settles once; while
its receipt is pending, the vanished cell is not given its old account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

structure FreeCut (reason : Terminal.Reason) (pid : PeerId) (skb : SkbId) (remaining : List SkbId)
    (history : List CausalJournal.Event) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (w : World) where
  ticket : Staged.Origins.Ticket
  position : Nat
  ordinal : Nat
  generation : Nat
  packet : DataPacket
  after : World
  next : Ledger
  entry : Accounted history ledger debts (⟨.unpublished,pid,skb::remaining⟩::locals) w.wg
  pending : (ticket,Status.pending (.allocated position ordinal))∈ledger
  origin : Origin history position ordinal generation skb packet
  native : (liftWG (freeTxSkb skb)).run w=.ok ((),after)
  assigned : next=settle [ticket]
    (.disposed (history++[CleanupPrimitive.readEvent w.wg skb,CleanupPrimitive.releaseEvent w.wg skb]).length reason) ledger
  step : Staged.Obligations.Step ledger next
  accounted : Accounted (CleanupPrimitive.finished reason skb w after history) next debts
    (⟨.unpublished,pid,remaining⟩::locals) after.wg
  terminal : (ticket,Status.terminal
    (.disposed (history++[CleanupPrimitive.readEvent w.wg skb,CleanupPrimitive.releaseEvent w.wg skb]).length reason))∈next

/-- Incoming same-ledger ownership and its actual allocation ticket make the
original getter/erase total. No successful cleanup or synthetic cut is assumed. -/
theorem free_cut (reason : Terminal.Reason)
    (before : Accounted history ledger debts (⟨.unpublished,pid,skb::remaining⟩::locals) w.wg)
    (batch : PendingBatch history ledger (skb::remaining)) :
    Nonempty (FreeCut reason pid skb remaining history ledger debts locals w) := by
  obtain ⟨ticket,position,ordinal,generation,packet,pending,origin⟩:=batch skb (List.mem_cons_self ..)
  have cell:=((before.entry.core.physical.resident ticket position ordinal pending).at_origin origin).2
  obtain ⟨v,events,cleanup⟩:=cleanup_total cell history
  have native : (liftWG (freeTxSkb skb)).run w=.ok ((),v) :=
    (FirstTerminal.cleanupFree_erases skb w history).symm.trans (congrArg Prod.fst cleanup)
  have fixed:=CleanupPrimitive.cleanup_run skb w v history native
  obtain ⟨_,step,accounted,terminal⟩:=CompleteCreate.labelled_free reason skb .unpublished
    fixed before pending origin
  refine ⟨{
    ticket:=ticket,position:=position,ordinal:=ordinal,generation:=generation,packet:=packet
    after:=v,next:=_,entry:=before,pending:=pending,origin:=origin,native:=native,assigned:=rfl
    step:=step,accounted:=?_,terminal:=terminal}⟩
  simpa only [CleanupPrimitive.finished,CleanupPrimitive.receipt,List.append_assoc,
    List.cons_append,List.nil_append] using accounted

theorem FreeCut.original (cut : FreeCut reason pid skb remaining history ledger debts locals w) :
    runPrefix (free reason skb) w history=
      (.ok ((),cut.after),CleanupPrimitive.finished reason skb w cut.after history) :=
  CleanupPrimitive.labelled_run reason skb w cut.after history cut.native

/-- Both post-erase positions are actual fixed native prefixes. The suffix
only emits the original saved release/terminal records on the same world. -/
theorem FreeCut.pending_receipt (cut : FreeCut reason pid skb remaining history ledger debts locals w)
    (phase : CleanupPrimitive.Phase) :
    runPrefix (CleanupPrimitive.atPhase phase w skb) w history=
      (.ok ((),cut.after),CleanupPrimitive.current phase w skb history) ∧
      PacketMaterial.view cut.after.wg skb=none ∧
      runPrefix (free reason skb) w history=
        runPrefix (CleanupPrimitive.due phase reason skb w cut.after) cut.after
          (CleanupPrimitive.current phase w skb history) ∧
      Accounted (CleanupPrimitive.finished reason skb w cut.after history) cut.next debts
        (⟨.unpublished,pid,remaining⟩::locals) cut.after.wg :=
  ⟨CleanupPrimitive.prefix_run phase skb w cut.after history cut.native,
    (FirstTerminal.cleanup_views skb w cut.after cut.native).2.1,
    CleanupPrimitive.original_suffix phase reason skb w cut.after history cut.native,cut.accounted⟩

theorem FreeCut.not_old_accounted
    (cut : FreeCut reason pid skb remaining history ledger debts locals w)
    (phase : CleanupPrimitive.Phase) :
    ¬Accounted (CleanupPrimitive.current phase w skb history) ledger debts
      (⟨.unpublished,pid,skb::remaining⟩::locals) cut.after.wg := by
  intro old
  have origin : Origin (CleanupPrimitive.current phase w skb history)
      cut.position cut.ordinal cut.generation skb cut.packet := by
    cases phase with
    | mutated=>exact cut.origin.append _
    | released=>exact cut.origin.append _
  have cell:=((old.entry.core.physical.resident cut.ticket cut.position cut.ordinal cut.pending).at_origin origin).2
  rw [(FirstTerminal.cleanup_views skb w cut.after cut.native).2.1] at cell
  cases cell

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
