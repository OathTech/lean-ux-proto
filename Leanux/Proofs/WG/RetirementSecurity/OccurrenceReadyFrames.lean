import Leanux.Proofs.WG.RetirementSecurity.OccurrenceKeepalive

/-! Source-local metadata writes preserve allocation freshness and physical
TX ownership. Each saved-peer setter is paired with its actual immediately
preceding read; arbitrary stale peer replacement is not a frame. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits OccurrenceStack

theorem peer_update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId)
    (queue : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Preserves (Ready locals active) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply RxPollOccurrences.join (modifyPeerKeysPrefix_erases pid f)
    (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient allocationAmbient (fun _ => True) pid f stamp))
  apply occurrence_passive
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    repeat' crypt_wire_step initial
  · intro initial
    change Preserves (fun w => handoffTxView w = initial) _
    repeat' first
      | (rx_retention_head setPeer
         apply (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptStagingFrames.«0».Leanux.Proofs.WG.RetirementSecurity.queue_set_saved)
         simp only [queue]
         assumption)
      | crypt_queue_step initial

theorem peer_update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (stamp : ∀p,(f p).internalId=p.internalId)
    (queue : ∀p,(f p).txQueue.all=p.txQueue.all)
    (next : ∀x,Preserves (Ready locals active) (tail x)) :
    Preserves (Ready locals active) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (peer_update pid f stamp queue) next

theorem modify_device (f : Device → Device)
    (identities : ∀w,identityView {w with dev:=w.dev.map f}=identityView w)
    (metadata : ∀w,allocationMetadata {w with dev:=w.dev.map f}=allocationMetadata w)
    (wire : ∀w,txCryptWire {w with dev:=w.dev.map f}=txCryptWire w)
    (queues : ∀w,handoffTxView {w with dev:=w.dev.map f}=handoffTxView w) :
    Preserves (Ready locals active) (modifyDev f) := by
  apply hoare_modify
  intro w before
  obtain ⟨h,allocated⟩ := before.1
  exact ⟨⟨h,allocated.congr (identities w) (metadata w)⟩,
    before.2.1.wire_queues (wire w) (queues w),
    before.2.2.frame_packets (congrArg Prod.fst (wire w))
      (fun _ owned => owned.queues (queues w)) (congrArg Prod.snd (wire w))⟩

macro "occurrence_ready_step" : tactic => `(tactic| first
  | (receive_update_head setPeer; apply peer_update <;> intro p <;> rfl)
  | (receive_update_head Bind.bind
     apply peer_update_bind
     · intro p; rfl
     · intro p; rfl
     intro x)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact RxPollOccurrences.store getDev_sameWGStore)
  | (rx_retention_head modifyDev
     apply modify_device
     · intro w; unfold identityView Peers.snapshot keypairResidents packetResidents; simp [Option.bind_map,Function.comp_def]
     · intro w; simp [allocationMetadata,deviceAllocationMetadata,Option.map_map,Function.comp_def] <;> rfl
     · intro w; simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,Option.map_map,Option.bind_map,Function.comp_def]
     · intro w; funext pid; simp [handoffTxView,Option.bind_map,Function.comp_def])
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | rxstack_preserves_join
  | rx_retention_step)

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
