import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPublicationSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueuedFrames

/-! Native projection facts for the actual publication borrow and head mark.
The packet-state write changes the full cell view, so it uses explicit
material, geometry and ownership preservation instead of a false equality. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation

theorem publication_borrow_view (items : List SkbId) : SameView StagedEntry.view (Publication.borrowNative items) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold Publication.borrowNative
  cases items.head? with
  | none => exact hoare_liftAmbient (AmbientM.invariant _) _
  | some first =>
    have read : SameView StagedEntry.view (getTxSkb first) := by
      apply (ProjectedAction.iff_run_ambient _ _ _).mpr
      intro w a packet v b run
      exact congrArg StagedEntry.view (Packets.getTxSkb_current first w v packet a b run).1
    apply hoare_bind _ _ (read initial)
    intro packet
    apply hoare_bind _ _ (indexOwner_peerDeref_preserves _ _)
    intro pid
    exact hoare_bind _ _ ((Queued.acquire pid).wp (· = initial)) (fun _ => preserves_pure _)

/-- Changing the published head state preserves the same ledger, packet
allocation identities and actual owning queue/local occurrences. -/
theorem publication_mark_native (first : SkbId) (state : PacketState)
    (before : Inv history ledger debts locals w) (a b : Ambient)
    (performed : ((setTxSkb first fun p => {p with state}).run w).run a = .ok (((),v),b)) :
    Inv history ledger debts locals v := by
  have epoch := (ProjectedAction.iff_run_ambient _ _ _).mp (PacketOrigins.skb_epoch _) w a () v b performed
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Staged.Exact.skb (SkbStore.setTx first fun p => {p with state})) w a () v b performed
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PacketMaterial.set_tx first (fun p => {p with state}) (fun _ => rfl)) w a () v b performed
  have ownership := (ProjectedAction.iff_run_ambient _ _ _).mp
    (ownershipPoints_holderStore _ (setTx_holderStore first (fun p => {p with state}) (fun _ => rfl)))
    w a () v b performed
  have core := before.core.quiet_views [] (by simp) epoch queues material
  simp only [List.append_nil] at core
  exact ⟨core,before.justified,before.allocationLinks,before.noSelected,
    (hoare_iff_run_ambient _ _ _).mp (Queue.mark_bounds first _) w a () v b before.packets performed,
    before.coverage.points ownership,before.inventory.points ownership⟩

theorem publication_mark_preserves (pid : PeerId) (first : SkbId) (state : PacketState) :
    Preserves (Inv history ledger debts locals) (publicationMarkNative pid first state) := by
  have mark : Preserves (Inv history ledger debts locals) (setTxSkb first fun p => {p with state}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b before run
    cases value
    exact publication_mark_native first state before a b run
  unfold publicationMarkNative
  apply hoare_bind _ _ (StagedEntry.native (Queued.read pid))
  intro peer
  split
  · apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.invariant _) _)
    intro ignored
    exact hoare_bind _ _ mark (fun _ => preserves_pure _)
  · exact hoare_bind _ _ mark (fun _ => preserves_pure _)

theorem publication_mark_erases (pid : PeerId) (first : SkbId) (state : PacketState) :
    ErasesPrefix (publicationMark pid first state) (liftWG (publicationMarkNative pid first state)) := by
  have step {α : Type} (action : WG.M α) :
      ErasesPrefix (Admission.actualOps.step action) (liftWG action) :=
    focusPrefix_erases _ _ (erasesPrefix_lift _)
  have access {α : Type} (action : MixedM α) (native : WG.M α)
      (erases : ErasesStatePrefix action native) :
      ErasesPrefix (Admission.actualOps.access action) (liftWG native) :=
    focusPrefix_erases _ _ (TxDisposition.nativeAccess_erases erases)
  have event : ErasesPrefix (Admission.actualOps.event (.published pid first state)) (pure ()) :=
    focusPrefix_erases _ _ (erasesPrefix_emit _)
  unfold publicationMark publicationMarkNative
  simp only [liftWG_bind,liftWG_pure,apply_ite]
  repeat' first
    | with_reducible exact step _
    | with_reducible exact access _ _ (getPeerMixed_erases _)
    | with_reducible exact access _ _ (setTxSkbPrefix_erases _ _)
    | exact event
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | with_reducible apply erasesPrefix_ite
    | split

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
