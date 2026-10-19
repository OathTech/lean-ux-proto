import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldChecked
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationAllocationCarrier

/-! The saved plaintext order determines the actual allocation ordinals.
Allocation is total once the selected peer's device exists, so no partial
unpublished batch can be hidden by an allocator Stop. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open Staged.Origins AuthenticatedEffects CausalJournal AllocatedObligation

theorem aligned_data (related : Ticket → Packet → Prop)
    (aligned : Aligned related tickets (packets.map DataPacket.plaintext))
    (owners : ∀ packet ∈ packets, packet.peer = pid) :
    Aligned (fun ticket packet => related ticket packet.plaintext ∧ packet.peer = pid) tickets packets := by
  induction packets generalizing tickets with
  | nil => cases aligned; exact .nil
  | cons packet packets ih =>
    cases aligned with
    | cons head tail =>
      exact .cons ⟨head,owners packet (List.mem_cons_self ..)⟩
        (ih tail (fun packet member => owners packet (List.mem_cons_of_mem _ member)))

/-- This relation includes the actual birth peer/allocation and original
plaintext, while the fixed ticket list preserves duplicate-payload ordinals. -/
theorem Held.allocation_alignment (before : Held ledger debts generation pid peer position history w a)
    (shape : BatchPayload.Shape pid kid peer.staged packets) :
    Aligned (fun ticket packet => Born history generation pid peer.internalId ticket packet.plaintext ∧
      packet.peer = pid) (pendingAt (.selected position) ledger) packets := by
  apply aligned_data
  · rw [shape.1]
    exact before.aligned
  · exact fun packet member => (shape.2 packet member).1

theorem allocate_total (packets : List DataPacket) (w : WGWorld) (a : Ambient)
    (device : w.dev = some d) :
    ∃ (items : List SkbId) (v : WGWorld) (last : Device),
      v.dev = some last ∧ ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),a) := by
  induction packets generalizing w d with
  | nil => exact ⟨[],w,d,device,rfl⟩
  | cons packet packets ih =>
    let next := {d with txSkbs := d.txSkbs.insert d.nextSkb packet,nextSkb := d.nextSkb+1}
    let u := Packets.update w (fun v => {v with txSkbs := v.txSkbs.insert d.nextSkb packet,nextSkb := d.nextSkb+1})
    have nextDevice : u.dev = some next := by simp [u,next,Packets.update,device]
    obtain ⟨items,v,last,atLast,rest⟩ := ih u nextDevice
    refine ⟨d.nextSkb :: items,v,last,atLast,?_⟩
    rw [List.mapM_cons,MaterialOrigin.bind_ok_ambient]
    refine ⟨d.nextSkb,u,a,Packets.newTxSkb_run w a d packet device,?_⟩
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨items,v,a,rest,rfl⟩

theorem allocation_observed (packets : List DataPacket) (w v : WGWorld) (a b : Ambient)
    (items : List SkbId) (native : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b))
    (history : List Event) :
    runWGPrefix (state (Journal.allocate packets)) w a history =
      (.ok ((items,v),b),history ++ [.old (.allocated packets ⟨items,w,v,a,b⟩)]) := by
  have raw := runWGPrefix_receiptWGObserved (liftWGPrefix (packets.mapM newTxSkb))
    (Journal.Event.allocated packets) w a (history.filterMap old?)
  rw [runWGPrefix_lift,native] at raw
  exact focusPrefix_suffix Event.old old? ((Journal.allocate packets).run w) a history
    (.ok ((items,v),b)) [.allocated packets ⟨items,w,v,a,b⟩] raw

/-- The actual allocator consumes the whole saved ordered batch and returns
its same fixed ledger at the recorded cut. The supplied native ownership and
allocation-frontier carriers remain explicit; no successful allocation premise
is used to hide a stopped partial batch. -/
theorem allocate_held (before : Held ledger debts generation pid peer position history w a)
    (shape : BatchPayload.Shape pid kid peer.staged packets)
    (bounded : Packets.Inv w)
    (ownership : RetirementSecurity.TxCoverage locals w)
    (inventory : RetirementSecurity.TxInventory locals w) :
    ∃ (items : List SkbId) (v : WGWorld),
      let receipt : WGRunWitness (List SkbId) := ⟨items,w,v,a,a⟩
      let events := history ++ [Event.old (.allocated packets receipt)]
      let after := assignBatch position history.length ledger
      runWGPrefix (state (Journal.allocate packets)) w a history = (.ok ((items,v),a),events) ∧
      receipt.Valid (packets.mapM newTxSkb) ∧ Staged.Obligations.Step ledger after ∧
      Core events after debts v ∧ pendingAt (.selected position) after = [] ∧
      RetirementSecurity.TxCoverage (⟨.unpublished,pid,items⟩ :: locals) v ∧
      RetirementSecurity.TxInventory (⟨.unpublished,pid,items⟩ :: locals) v := by
  have epoch := before.vacant.1
  cases device : w.dev with
  | none => simp [Packets.epoch,device] at epoch
  | some d =>
    obtain ⟨items,v,last,_,native⟩ := allocate_total packets w a device
    have result := core_allocate (run := ⟨items,w,v,a,a⟩) before.core bounded ownership inventory
      pid packets native device (before.allocation_alignment shape)
    exact ⟨items,v,allocation_observed packets w v a a items native history,native,result⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldFrontier
