import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreCompositionFrames

/-! A stopped checked-send continuation retains a concrete native take cut.
Only nonce and selection receipts may follow that cut while it owns the saved
batch. Restoration, allocation and disposal must establish their own frontier;
an arbitrary historical ledger is not an active selected-batch certificate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Staged.Origins AuthenticatedEffects CausalJournal
open HandshakeSecurity.StagedConservation

def progress : Event → Bool
  | .old (.nonce _) | .old (.reserved _ _) | .old (.responder (.selected _ _)) => true
  | _ => false

def blocking? (event : Event) : Option Event := if progress event then none else some event

theorem progress_quiet (allowed : progress event = true) : birthPackets event = [] := by
  cases event <;> try rfl
  case old value =>
    cases value <;> try rfl
    case routed => cases allowed
  case keepalivePrepared => cases allowed

structure Anchor (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) (history : List Event) : Prop where
  reached : ∃ (past suffix : List Event) (r : Take.Receipt),
    history = (past ++ [.stagingTaken r]) ++ suffix ∧
    position = past.length ∧ r.pid = pid ∧ r.Valid ∧ r.run.value = some peer ∧
    Core (past ++ [.stagingTaken r]) ledger debts r.run.after ∧
    RestoreEntry.Vacant generation pid peer.internalId r.run.after ∧
    Aligned (Born (past ++ [.stagingTaken r]) generation pid peer.internalId)
      (pendingAt (.selected position) ledger) peer.staged ∧
    ∀ event ∈ suffix, progress event = true

theorem Anchor.append (before : Anchor ledger debts generation pid peer position history)
    (later : ∀ event ∈ suffix, progress event = true) :
    Anchor ledger debts generation pid peer position (history ++ suffix) := by
  obtain ⟨past,old,r,eq,positionEq,pidEq,native,chosen,core,vacant,aligned,allowed⟩ := before.reached
  refine ⟨past,old ++ suffix,r,?_,positionEq,pidEq,native,chosen,core,vacant,aligned,?_⟩
  · simp only [eq,List.append_assoc]
  · intro event member
    exact (List.mem_append.mp member).elim (allowed event) (later event)

/-- The checkpoint accounts for every canonical birth, including selected
tickets, and keeps both directions of allocated-cell/debt coverage. Its world
is the recorded native take world, not an invented post-Stop world. -/
theorem Anchor.accounted (before : Anchor ledger debts generation pid peer position history) :
    ∃ (r : Take.Receipt), r.Valid ∧ r.run.value = some peer ∧
      Core history ledger debts r.run.after ∧
      Aligned (Born history generation pid peer.internalId)
        (pendingAt (.selected position) ledger) peer.staged := by
  obtain ⟨past,suffix,r,eq,_,_,native,chosen,core,_,aligned,allowed⟩ := before.reached
  subst history
  exact ⟨r,native,chosen,core.quiet_views suffix
    (fun event member => progress_quiet (allowed event member)) rfl rfl rfl,
    aligned.history_append suffix⟩

structure Held (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (history : List Event) (w : WGWorld) (_ : Ambient) : Prop where
  core : Core history ledger debts w
  vacant : RestoreEntry.Vacant generation pid peer.internalId w
  aligned : Aligned (Born history generation pid peer.internalId)
    (pendingAt (.selected position) ledger) peer.staged
  anchor : Anchor ledger debts generation pid peer position history

theorem Held.views_append (before : Held ledger debts generation pid peer position history w a)
    (suffix : List Event) (allowed : ∀ event ∈ suffix, progress event = true)
    (epoch : Packets.epoch v = Packets.epoch w) (queues : stagedAt v = stagedAt w)
    (cells : PacketMaterial.view v = PacketMaterial.view w) :
    Held ledger debts generation pid peer position (history ++ suffix) v b :=
  ⟨before.core.quiet_views suffix (fun event member => progress_quiet (allowed event member)) epoch queues cells,
    before.vacant.views epoch queues,before.aligned.history_append suffix,before.anchor.append allowed⟩

/-- Native take initializes this frontier at its own position, before key
borrowing. The same fixed tickets and physical backing remain on both sides. -/
theorem taken (r : Take.Receipt) (native : r.Valid) (chosen : r.run.value = some peer)
    (before : Core history ledger debts r.run.before) :
    ∃ after generation, Step ledger after ∧
      Held after debts generation r.pid peer history.length
        (history ++ [.stagingTaken r]) r.run.after r.run.ambientAfter := by
  obtain ⟨after,accounted,core⟩ := core_take r native before
  have transfer := accounted.exactTransfer
  rw [chosen] at transfer
  obtain ⟨generation,epoch,_,_,aligned⟩ := transfer
  obtain ⟨_,_,same,_,empty,_⟩ := take_receipt_views r native peer chosen
  have vacant : RestoreEntry.Vacant generation r.pid peer.internalId r.run.after := ⟨same.trans epoch,empty⟩
  refine ⟨after,generation,accounted.step,core,vacant,aligned,?_⟩
  exact ⟨history,[],r,by simp,rfl,rfl,native,chosen,core,vacant,aligned,by simp⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldFrontier
