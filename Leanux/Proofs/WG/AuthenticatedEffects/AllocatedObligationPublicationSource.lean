import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionSource
import Leanux.Proofs.WG.Queues.TxPublication

/-! Exact publication cuts before borrowing, before publication and before
repayment. No new journal event or mirror operation is introduced. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Publication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def borrow (items : List SkbId) : PrefixM CausalJournal.Event (SkbId × PeerId) := do
  let some first := items.head? | Admission.actualOps.step (invariant "an empty ring item")
  let pid ← Admission.actualOps.access
    (peerDerefPrefix (.keypair (← Admission.actualOps.access (getTxSkbPrefix first)).keypair))
  Admission.actualOps.access (peerGetMixed pid)
  return (first,pid)

def borrowNative (items : List SkbId) : WG.M (SkbId × PeerId) := do
  let some first := items.head? | invariant "an empty ring item"
  let pid ← IndexOwner.peerDeref (.keypair (← getTxSkb first).keypair)
  peerGet pid
  return (first,pid)

def middle (pid : PeerId) (first : SkbId) (state : PacketState) : PrefixM CausalJournal.Event Unit := do
  if !((← Admission.actualOps.access (getPeerMixed pid)).txQueue.all.any (·.head? == some first)) then
    Admission.actualOps.step (invariant "an item for the tx worker that is not on its peer's tx_queue")
  Admission.actualOps.access (setTxSkbPrefix first fun p => {p with state})
  Admission.actualOps.event (.published pid first state)
  _ ← Admission.actualOps.access (cpumaskChooseOnlinePrefix pid)
  if !(← Admission.actualOps.step getDev).txWorkQueue.contains pid ||
      (← Admission.actualOps.step (peekQueuedUnit .txWorker pid)) then
    Admission.actualOps.step (recordQueued .txWorker pid)
    Admission.actualOps.step (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})

theorem factor (items : List SkbId) (state : PacketState) :
    TxSource.publish Admission.actualOps items state = (do
      let (first,pid) ← borrow items
      middle pid first state
      Admission.actualOps.release (some pid)) := by
  unfold TxSource.publish borrow
  cases items.head? with
  | none => rfl
  | some first =>
    simp only [middle,bind_assoc,TxDisposition.bind_ite,pure_bind]

theorem borrow_erases (items : List SkbId) :
    ErasesPrefix (borrow items) (liftWG (borrowNative items)) := by
  unfold borrow borrowNative
  cases items.head? with
  | none => exact focusPrefix_erases _ _ (erasesPrefix_lift _)
  | some first =>
    simp only [liftWG_bind,liftWG_pure]
    apply erasesPrefix_bind (focusPrefix_erases _ _
      (TxDisposition.nativeAccess_erases (getTxSkbPrefix_erases first)))
    intro packet
    apply erasesPrefix_bind (focusPrefix_erases _ _
      (TxDisposition.nativeAccess_erases (peerDerefPrefix_erases _)))
    intro pid
    apply erasesPrefix_bind (focusPrefix_erases _ _
      (TxDisposition.nativeAccess_erases (peerGetMixed_erases pid)))
    intro _
    exact erasesPrefix_pure _

theorem middle_erases (pid : PeerId) (first : SkbId) (state : PacketState) :
    ErasesPrefix (middle pid first state)
      (liftWG (TxDisposition.publicationMiddle pid first state)) := by
  have step {α : Type} (action : WG.M α) :
      ErasesPrefix (Admission.actualOps.step action) (liftWG action) :=
    focusPrefix_erases _ _ (erasesPrefix_lift _)
  have access {α : Type} (action : MixedM α) (native : WG.M α)
      (erases : ErasesStatePrefix action native) :
      ErasesPrefix (Admission.actualOps.access action) (liftWG native) :=
    focusPrefix_erases _ _ (TxDisposition.nativeAccess_erases erases)
  have cut {α : Type} {g : PrefixM CausalJournal.Event α} {a : StateT World (Except Stop) α}
      (rest : ErasesPrefix g a) :
      ErasesPrefix (Admission.actualOps.event (.published pid first state) >>= fun _ => g) a := by
    have quiet : ErasesPrefix (Admission.actualOps.event (.published pid first state)) (pure ()) :=
      focusPrefix_erases _ _ (erasesPrefix_emit _)
    simpa only [pure_bind] using erasesPrefix_bind quiet (fun _ => rest)
  unfold middle TxDisposition.publicationMiddle
  simp only [liftWG_bind,liftWG_pure,apply_ite]
  repeat' first
    | with_reducible exact step _
    | with_reducible exact access _ _ (getPeerMixed_erases _)
    | with_reducible exact access _ _ (setTxSkbPrefix_erases _ _)
    | with_reducible exact access _ _ (cpumaskChooseOnlinePrefix_erases _)
    | with_reducible apply cut
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | with_reducible apply erasesPrefix_ite
    | split

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Publication
