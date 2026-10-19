import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedSettlement
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionGeometry
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionSocket
import Leanux.Proofs.WG.TransmitSecurity.StagedSocketSendFrames

/-! The actual native socket result advances the selected cursor and the
canonical semantic ledger together. Its source receipt and allocation lineage
refer to the packet read at this same native send entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity StagedProvenance Queues.RxCredits

theorem socket_entry_view (receipt : Completion.SocketReceipt) (native : receipt.Valid) :
    StagedEntry.view receipt.socket.after.wg = StagedEntry.view receipt.socket.before.wg := by
  have geometry : SameView StagingOccurrences.geometry receipt.action := by
    unfold Completion.SocketReceipt.action
    cases receipt.ipv4
    · exact CompletionGeometry.send6_geometry _ _ _ _ _
    · exact CompletionGeometry.send4_geometry _ _ _ _ _
  have staged : SameView Staged.stagedAt receipt.action := by
    unfold Completion.SocketReceipt.action
    cases receipt.ipv4
    · exact Staged.Exact.send6_staged _ _ _ _ _
    · exact Staged.Exact.send4_staged _ _ _ _ _
  have lift_frame {σ : Type} (view : WGWorld → σ) (frame : SameView view receipt.action) :=
    (ProjectedAction.iff_run _ _ _).mp
      (sameView_liftWG (fun w : World => view w.wg) view receipt.action frame (fun _ _ _ same => same))
      _ _ _ native.2.2
  have shape := lift_frame _ geometry
  have queues := lift_frame _ staged
  have owner := lift_frame _ (socket_ownership receipt)
  have handoff : handoffTxView receipt.socket.after.wg = handoffTxView receipt.socket.before.wg := by
    funext pid
    have fields := congrArg (Option.map (fun p : PeerOwnership => p.2.1))
      (congrFun (congrArg (fun x => x.2.2.1) owner) pid)
    simpa only [ownershipPointView,ownershipAt,handoffTxView,peerOwnership,peerAt,
      Option.map_map,Function.comp_def] using fields
  have owners := queueContents_of_exact handoff
  obtain ⟨epoch,packets,material⟩ := FirstTerminal.socket_views receipt native
  have snapshot := congrArg Prod.fst shape
  change Packets.snapshot receipt.socket.after.wg = Packets.snapshot receipt.socket.before.wg at snapshot
  simp only [StagedEntry.view,epoch,queues,material,snapshot,packets,owners]

theorem completion_encode_births (event : Completion.Event) :
    birthPackets (FirstTerminal.encode event) = [] := by cases event <;> rfl

theorem PacketAt.before_current (current : PacketAt skb packet w) : packet.before.wg = w.wg :=
  (read_cell packet current.1).1.symm.trans current.2.1

/-- The actual socket result, including errno, settles the same allocated
head ticket and retains a physical cleanup debt in the full entry bundle. -/
theorem indexed_inner_advanced
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (packetAt : PacketAt skb packet w)
    (peerValid : peer.Valid (liftWG (getPeer context.pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody context.pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle)) :
    let receipt : Completion.SocketReceipt := ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩
    let prior := history ++ middle.map FirstTerminal.encode
    let outcome := Staged.Obligations.Terminal.socket prior.length (ret == 0)
    let journal := prior ++ [CausalJournal.Event.old (.socket receipt)]
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      runPrefix (FirstTerminal.focused (Completion.socket context.pid skb packet peer ipv4)) w history =
        (.ok (ret,v),journal) ∧
      Owned context (.sending rest) journal (settle [chosen.ticket] outcome ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) v := by
  dsimp only
  obtain ⟨native,observed⟩ := FirstTerminal.inner_cut context.pid skb packet peer ipv4 w v history middle ret
    packetAt.1 peerValid performed
  have member : skb ∈ context.items := by
    obtain ⟨left,equal⟩ := before.cursor.remaining
    rw [← equal]
    simp [Phase.remaining]
  obtain ⟨chosen,inside,head⟩ := List.mem_map.mp member
  have kept := before.append (middle.map FirstTerminal.encode) (by
    intro event member
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp member
    exact completion_encode_births e)
  have pending := (kept.cursor.assigned chosen inside).1 (by simp [head])
  have origin : Origin (history ++ middle.map FirstTerminal.encode) chosen.position chosen.ordinal
      chosen.generation skb chosen.value := by
    simpa only [Binding.recorded,head] using kept.cursor.recorded chosen inside
  have backed := kept.entry.core.physical.resident chosen.ticket chosen.position chosen.ordinal pending
  have atRead : Backed (history ++ middle.map FirstTerminal.encode) chosen.position chosen.ordinal packet.before.wg := by
    rw [packetAt.before_current]
    exact backed
  have evidence : At (history ++ middle.map FirstTerminal.encode)
      (CausalJournal.Event.old (.socket ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩)) chosen.ticket
      (.socket (history ++ middle.map FirstTerminal.encode).length (ret == 0)) :=
    .socket _ native chosen.position chosen.ordinal chosen.generation chosen.value
      ((kept.entry.allocationLinks chosen.ticket chosen.position chosen.ordinal pending).at_origin origin) atRead
  have after := kept.same_view (socket_entry_view _ native)
  exact ⟨chosen,inside,head,observed,after.settle_head chosen inside head evidence rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
