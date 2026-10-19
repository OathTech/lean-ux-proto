import Leanux.Proofs.WG.RetirementSecurity.InitializedRetirement

/-! The actual cached peek, readiness test, packet getter and dequeue move
one RX key credit from its durable queue occurrence to the selected local.
All source runs share their intermediate world and ambient states. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NativeRxSelection
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

/-- Fields unchanged by native receive selection, before its key payment. -/
def wire (w : WGWorld) := (keyReferenceView w,RxDisposition.nativeRxStore w)

theorem stored {action : WG.M α} (same : SameWGStore action) : SameView wire action :=
  same.of_factor (fun s : WGStoreView=>wire {dev:=s.dev}) wire (fun _=>rfl)

theorem set_peer (pid : PeerId) (p : Peer) : SameView wire (setPeer pid p) := by
  intro initial
  unfold setPeer modifyDev
  apply hoare_modify
  intro w before
  unfold wire keyReferenceView keyAt RxDisposition.nativeRxStore at *
  simpa only [Option.bind_map,Option.map_map,Function.comp_def] using before

macro "rx_selection_wire_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head setPeer; exact (set_peer _ _).wp (·=$initial))
  | (rx_retention_head PrevQueue.peek; exact (stored (prevQueuePeek_sameWGStore _)).wp (·=$initial))
  | rx_retention_step)

theorem peek_wire (pid : PeerId) : SameView wire (peekRxQueue pid) := by
  intro initial
  change Preserves (fun w=>wire w=initial) _
  unfold peekRxQueue
  repeat' rx_selection_wire_step initial

theorem drop_wire (pid : PeerId) : SameView wire (dropRxQueue pid) := by
  intro initial
  change Preserves (fun w=>wire w=initial) _
  unfold dropRxQueue
  repeat' rx_selection_wire_step initial

/-- This is exactly the original poll's readiness expression. -/
def ready (first : Option SkbId) : WG.M Bool :=
  WG.andM (branch .rxPollPacket first.isSome) do
    let some id := first | invariant "unreachable"
    branch .rxPollNotUncrypted ((←getRxSkb id).state != .uncrypted)

/-- Original successive selection cuts derive a real detached, funded RX
local, retaining both allocation identity and the incoming key reference
counts. No numeric peer count is used to manufacture key funding. -/
theorem selected (keys : HolderAccount [] w) (carriers : CarrierState entries loans w)
    (pid id : Nat) (pkt : RxPacket) (a b c d e : Ambient)
    (peek : ((peekRxQueue pid).run w).run a=.ok ((some id,u),b))
    (test : ((ready (some id)).run u).run b=.ok ((true,t),c))
    (read : ((getRxSkb id).run t).run c=.ok ((pkt,s),d))
    (drop : ((dropRxQueue pid).run s).run d=.ok (((),v),e)) :
    ∃allocation,pkt.keypair=allocation.slot ∧ HolderAccount [allocation] v ∧
      RxDetached id v ∧ pkt.state≠.uncrypted ∧ wire v=wire w := by
  obtain ⟨sameT,rd,rpkt,rdFound,rpktFound,readyFlag⟩ := ready_result (some id) u t true b c test
  subst t
  obtain ⟨sameS,sameD,sd,sdFound,packet⟩ := Packets.getRxSkb_current id u s pkt c d read
  subst s
  subst d
  have sameDev : rd=sd := Option.some.inj (rdFound.symm.trans sdFound)
  subst rd
  have samePacket : rpkt=pkt := Option.some.inj (rpktFound.symm.trans packet)
  subst rpkt
  have notUncrypted : pkt.state≠.uncrypted := by
    intro same
    rw [same] at readyFlag
    change true=false at readyFlag
    cases readyFlag
  have peekKeys := (keys.peek_rx pid a b peek).1
  obtain ⟨peekCarriers,dd,p,device,peer,peeked⟩ := peek_state pid carriers a b peek
  have sameDevice : dd=sd := Option.some.inj (device.symm.trans sdFound)
  subst dd
  obtain ⟨allocation,loan,localKeys,_,detached⟩ :=
    peekKeys.drop_rx_carrier peekCarriers device peer peeked c e drop
  have named : nameLoan u (.receive pid id) pkt.keypair=some ⟨.receive pid id,allocation⟩ := by
    simpa [receiveLoan,device,packet] using loan
  exact ⟨allocation,(nameLoan_resident named).2.1.symm,localKeys,detached,notUncrypted,
    ((ProjectedAction.iff_run_ambient _ _ _).mp (drop_wire pid) u c () v e drop).trans
      ((ProjectedAction.iff_run_ambient _ _ _).mp (peek_wire pid) w a (some id) u b peek)⟩

theorem initialized_selected (trace : Runner.Trace) (placeholders : Bool)
    (initialized : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (pid id : Nat) (pkt : RxPacket) (b c d e : Ambient)
    (peek : ((peekRxQueue pid).run w.wg).run w.ambient=.ok ((some id,u),b))
    (test : ((ready (some id)).run u).run b=.ok ((true,t),c))
    (read : ((getRxSkb id).run t).run c=.ok ((pkt,s),d))
    (drop : ((dropRxQueue pid).run s).run d=.ok (((),v),e)) :
    ∃allocation,pkt.keypair=allocation.slot ∧ HolderAccount [allocation] v ∧
      RxDetached id v ∧ pkt.state≠.uncrypted ∧ wire v=wire w.wg := by
  obtain ⟨entries,whole⟩ := HolderInitialized.initialized trace placeholders initialized
  obtain ⟨holders,funded,_⟩ := whole.1.1.1.1
  exact selected whole.2.1 funded.carriers pid id pkt w.ambient b c d e peek test read drop

end Leanux.Proofs.WG.RetirementSecurity.NativeRxSelection
