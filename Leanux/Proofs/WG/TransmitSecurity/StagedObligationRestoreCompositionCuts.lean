import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreCompositionFrames

/-! Actual take and restore receipts transfer the same fixed ledger. Borrowing
does not remove the caller's selected obligations; restoration prepends their
original packets to the source-derived empty target. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreComposition
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open Staged.Origins AuthenticatedEffects.CausalJournal
open HandshakeSecurity.StagedConservation

/-- Immediately after the actual take, the selected ticket list is exactly the
incoming staged list. Neither a completed key borrow nor a completed send is
assumed. The selected-location freshness premise belongs to the local ledger. -/
theorem taken_held (r : Take.Receipt) (run : r.Valid) (peer : Peer)
    (selected : r.run.value = some peer) (valid : Valid births ledger)
    (before : QueueInv history ledger r.run.before)
    (epoch : Packets.epoch r.run.before = some generation) (position : Nat)
    (unused : pendingAt (.selected position) ledger = []) :
    let source := Pending.staged generation r.pid peer.internalId
    let after := transferLocation source (.selected position) ledger
    Step ledger after ∧ Valid births after ∧
      Held after generation r.pid peer position history r.run.after r.run.ambientAfter ∧
      pendingAt (.selected position) after = pendingAt source ledger := by
  dsimp only
  have transfer := take_step r run peer selected valid before epoch position unused
  obtain ⟨_,_,same,_,empty,_⟩ := take_receipt_views r run peer selected
  refine ⟨transfer.1,transfer.2.1,?_,transfer.2.2.2.1⟩
  refine ⟨transfer.2.2.1,⟨same.trans epoch,empty⟩,?_⟩
  rw [transfer.2.2.2.1]
  exact transfer.2.2.2.2.1

theorem borrow_held (ledger : Ledger) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) :
    StatePrefixEnsures (Held ledger generation pid peer position) (fun _ => True)
      (liftWGPrefix (Take.borrow (some peer)))
      (fun selected h w a => ∃ keypair, selected = some (peer,keypair) ∧
        Held ledger generation pid peer position h w a) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ _ => True.intro)
  intro h w a chosen v b before run
  unfold Take.borrow at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨keypair,u,c,borrowed,returned⟩ := run
  have epoch := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PacketOrigins.epoch_ring ((RetirementSecurity.keyGet_cryptWire peer.keypairCurrent).factor Prod.fst))
    w a keypair u c borrowed
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp (key_get_staged peer.keypairCurrent)
    w a keypair u c borrowed
  have kept : Held ledger generation pid peer position h u c := by
    simpa only [List.append_nil] using before.views_append (b := c) [] epoch queues
  simp only [StateT.run_pure,CounterWindow.except_pure,Except.ok.injEq,Prod.mk.injEq] at returned
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := returned
  exact ⟨keypair,rfl,kept⟩

def Restored (births : List Ticket) (ledger : Ledger) (generation : Nat)
    (pid : PeerId) (peer : Peer) (position : Nat)
    (history : List Event) (w : WGWorld) (_ : Ambient) : Prop :=
  let source := Pending.selected position
  let target := Pending.staged generation pid peer.internalId
  let after := transferLocation source target ledger
  Step ledger after ∧ Valid births after ∧ QueueInv history after w ∧
    pendingAt source after = [] ∧ pendingAt target after = pendingAt source ledger

/-- At the actual restore receipt, the source-derived vacancy discharges the
empty-target premise. The same selected tickets return to the same peer
allocation; the unchanged old terminal entries follow from Step. The native
history is kept even when a later queueing callback stops. -/
theorem restore_observed (record : Restore.Receipt → Event) (ledger : Ledger)
    (valid : Valid births ledger) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) :
    StatePrefixEnsures (Held ledger generation pid peer position) (fun _ => True)
      (Restore.observed record pid peer.staged)
      (fun _ => Restored births ledger generation pid peer position) := by
  intro w a h before
  unfold Restore.observed
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (Restore.nativeRestore pid peer.staged))
    (fun run => record ⟨pid,peer.staged,run⟩) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((Restore.nativeRestore pid peer.staged).run w).run a with
  | error stop => exact ⟨[],by simp,True.intro,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    cases value
    let r : Restore.Receipt := ⟨pid,peer.staged,⟨(),w,v,a,b⟩⟩
    have transfer := restore_empty_step r run valid before.queues
      before.vacant.1 before.vacant.2 position before.aligned
    refine ⟨[record r],rfl,True.intro,?_⟩
    exact ⟨transfer.1,transfer.2.1,transfer.2.2.1.append_history [record r],
      transfer.2.2.2.1,transfer.2.2.2.2⟩

theorem no_key_restores (record : Restore.Receipt → Event) (ledger : Ledger)
    (valid : Valid births ledger) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (keypair : Option KeypairId) (invalid : Bool)
    (o : AuthenticatedEffects.TimerEffects.Ops (WGPrefix Event))
    (native : ∀ {α} (action : WG.M α), o.step action = liftWGPrefix action)
    (queue : PeerId → Bool → WGPrefix Event Unit) (Post : List Event → WGWorld → Ambient → Prop)
    (queued : StatePrefixEnsures (Restored births ledger generation pid peer position) (fun _ => True)
      (queue pid false) (fun _ => Post)) :
    StatePrefixEnsures (Held ledger generation pid peer position) (fun _ => True)
      (Restore.noKeyWith o (Restore.observed record) queue pid peer.staged keypair invalid) (fun _ => Post) := by
  rw [RestoreEntry.no_key_factor]
  have step : @o.step = (fun {α} (action : WG.M α) => (liftWGPrefix action : WGPrefix Event α)) := by
    funext α action
    exact native action
  rw [step]
  exact StatePrefixEnsures.bind (prefix_held peer.staged keypair invalid) (fun _ =>
    StatePrefixEnsures.bind (restore_observed record ledger valid generation pid peer position) (fun _ => queued))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreComposition
