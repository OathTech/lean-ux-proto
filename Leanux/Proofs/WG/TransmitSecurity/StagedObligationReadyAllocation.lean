import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadySource
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSoundAllocation

/-! The actual allocator closes the selected carrier into a complete entry
bundle with one unpublished native batch. Allocation bounds are transported
through every concrete newTxSkb, rather than assumed again after allocation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance RetirementSecurity AllocatedObligation

theorem allocated_bounds (packets : List DataPacket) (before : Packets.Inv w)
    (a b : Ambient) (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    Packets.Inv v := by
  induction packets generalizing w a items with
  | nil => simp only [List.mapM_nil] at run; cases run; exact before
  | cons first rest ih =>
    simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨id,u,c,head,tail,t,e,remaining,done⟩ := run
    cases done
    exact ih ((Action.iff_run_ambient _ _ _).mp (Packets.newTxSkb_contract first)
      w a id u c before head).1 c remaining

/-- The full entry bundle at this concrete allocation cut is derived from
the selected caller and its exact nonce-loop packet shape. Every selected
location is empty; the returned IDs own one unpublished native batch. -/
theorem allocate (before : Ready ledger debts locals generation pid peer position history w a)
    (shape : BatchPayload.Shape pid kid peer.staged packets) :
    ∃ (items : List SkbId) (v : WGWorld),
      let receipt : WGRunWitness (List SkbId) := ⟨items,w,v,a,a⟩
      let events := history ++ [Event.old (.allocated packets receipt)]
      let after := assignBatch position history.length ledger
      runWGPrefix (state (Journal.allocate packets)) w a history = (.ok ((items,v),a),events) ∧
      receipt.Valid (packets.mapM newTxSkb) ∧ Step ledger after ∧
      StagedEntry.Inv events after debts (⟨.unpublished,pid,items⟩ :: locals) v := by
  obtain ⟨items,v,performed,native,step,core,justified,links,idle,coverage,inventory⟩ :=
    SoundHeld.allocate before.toSound shape before.native.1 before.native.2.1 before.native.2.2
  exact ⟨items,v,performed,native,step,core,justified,links,idle,
    allocated_bounds packets before.native.1 a a native,coverage,inventory⟩

theorem acquire_peer {Safe : List Event → Prop}
    (frontier : ∀ h, SoundHeld.Active ledger debts generation pid peer position h → Safe h)
    (owner : PeerId) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe
      (liftWGPrefix (peerGet owner)) :=
  decorate (SoundHeld.decorate frontier (HeldFrontier.held_lift (fun _ => id) _
    (PacketOrigins.epoch_ring (TxRing.peerGet_frame owner)) (Staged.Exact.peer_get owner)
    (PacketMaterial.of_packets (TxDisposition.peerGet_packets owner))))
    (erasesStatePrefix_lift _) (NativeReady.get_peer owner)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
