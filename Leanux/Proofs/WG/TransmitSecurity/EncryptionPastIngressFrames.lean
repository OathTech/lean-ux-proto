import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastNapi
import Leanux.Proofs.WG.Queues.TxLiveIngress

/-! Ingress allocation increases the shared packet frontier without admitting
TX aliases. Nullable peer/index borrowing and RX writes preserve the supplied
historical exclusion; failed native prefixes assert no returned World. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem ready_allocator (action : PacketAllocation) :
    Preserves (Ready past active) action.original := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have live := (hoare_iff_run_ambient _ _ _).mp (LiveFrontier.allocator_ready action)
    w a result v b before.1 run
  rw [action.run] at run
  cases device : w.dev with
  | none => simp only [device] at run; cases run
  | some d =>
    simp only [device,Except.ok.injEq,Prod.mk.injEq] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    refine ⟨live,before.2.1,?_⟩
    intro label member
    apply (before.2.2 label member).shrink (t := view (Packets.update w action.device))
      (Nat.le_refl _)
    intro current found
    have same : current = ⟨d.ifindex,d.nextSkb + 1,d.encryptQueue.items⟩ := by
      cases action <;> simpa only [view,Packets.update,PacketAllocation.device,
        device,Option.map_some,Option.some.injEq] using found.symm
    subst current
    refine ⟨⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩,by simp [view,device],rfl,
      Nat.le_succ _,fun _ h => h⟩

theorem ready_set_rx (id : SkbId) (f : RxPacket → RxPacket) :
    Preserves (Ready past active) (setRxSkb id f) :=
  ready_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveIngress.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveIngress.setRx) id f)
    (set_rx id f)

theorem ready_maybe_get (peer : Option PeerId) :
    Preserves (Ready past active) (peerGetMaybeZero peer) := by
  unfold peerGetMaybeZero refcountIncNotZero requireNotPending
  simp (config := {zeta := false}) only [branch,branchCmp,unsupported,invariant]
  repeat' encryption_past_receive_step

theorem ready_owner_word (owner : IndexOwner) (peer : Option PeerId) :
    Preserves (Ready past active) (owner.setPeerWord peer) := by
  cases owner <;> unfold IndexOwner.setPeerWord
  all_goals repeat' encryption_past_receive_step

theorem ready_acquire_owner (owner : IndexOwner) :
    Preserves (Ready past active) (Affiliation.acquireOwner owner) :=
  preserves_bind (indexOwner_peerWord_preserves owner (Ready past active)) (fun peer =>
    preserves_bind (ready_maybe_get peer) (fun taken =>
      preserves_bind (ready_owner_word owner taken) (fun _ => preserves_pure _)))

theorem ready_index_lookup (kinds : List IndexKind) (index : Nat) :
    Preserves (Ready past active) (indexLookup kinds index) := by
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Affiliation.acquireOwner; exact ready_acquire_owner _)
    | (rx_retention_head liftIndex; exact ready_index _)
    | encryption_past_receive_step

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
