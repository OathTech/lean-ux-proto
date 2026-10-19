import Leanux.Proofs.WG.RetirementSecurity.ConditionalRetirement
import Leanux.Proofs.WG.RetirementSecurity.FinalRxSelection

/-! The clear worker and final DEAD receive disposal form one contiguous
native source chain. Its post-clear account is derived from the original
initialized endpoint; the selection phase does not fabricate new key credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ConditionalRetirement
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

/-- Receive selection preserves the actual key counts and packet cells even
while it detaches a queue occurrence. This frame needs no funding assumption. -/
theorem rx_selection_wire (pid id : Nat) (pkt : RxPacket) (a b c d e : Ambient)
    (peek : ((peekRxQueue pid).run w).run a=.ok ((some id,u),b))
    (test : ((NativeRxSelection.ready (some id)).run u).run b=.ok ((true,t),c))
    (read : ((getRxSkb id).run t).run c=.ok ((pkt,s),d))
    (drop : ((dropRxQueue pid).run s).run d=.ok (((),v),e)) :
    NativeRxSelection.wire v=NativeRxSelection.wire w := by
  obtain ⟨sameT,_⟩ := ready_result (some id) u t true b c test
  subst t
  obtain ⟨sameS,sameD,_⟩ := Packets.getRxSkb_current id u s pkt c d read
  subst s
  subst d
  exact ((ProjectedAction.iff_run_ambient _ _ _).mp (NativeRxSelection.drop_wire pid) u c () v e drop).trans
    ((ProjectedAction.iff_run_ambient _ _ _).mp (NativeRxSelection.peek_wire pid) w a (some id) u b peek)

theorem dead_rx (account : HolderAccount [] w)
    (allocation : Credits.Allocation) (projected : durableLoans w=some loans)
    (last : (loans.map (·.allocation)).count allocation=1)
    (pid id : Nat) (pkt : RxPacket) (owner : pkt.peer=pid) (key : pkt.keypair=allocation.slot)
    (dead : pkt.state=.dead) (a b c d e f g : Ambient)
    (peek : ((peekRxQueue pid).run w).run a=.ok ((some id,u),b))
    (test : ((NativeRxSelection.ready (some id)).run u).run b=.ok ((true,t),c))
    (read : ((getRxSkb id).run t).run c=.ok ((pkt,s),d))
    (drop : ((dropRxQueue pid).run s).run d=.ok (((),v),e))
    (stateCheck : ((branch .rxPollNotCrypted (pkt.state != .crypted) : WG.M Bool).run v).run e=
      .ok ((skip,z),f))
    (dispose : ((do
      keypairPut (some pkt.keypair) false
      peerPut (some pid)
      _←branch .rxPollFree true
      freeRxSkb id : WG.M Unit).run z).run f=.ok (((),final),g)) :
    skip=true ∧ keyAt final allocation.slot=none := by
  have wire := rx_selection_wire pid id pkt a b c d e peek test read drop
  obtain ⟨actual,named,credits⟩ := account
  have same : actual=loans := Option.some.inj (named.symm.trans projected)
  subst actual
  simp only [List.append_nil] at credits
  have paid := credits.reference_view (congrArg Prod.fst wire)
  have checked : skip=true ∧ z=v := by
    rw [dead] at stateCheck
    cases stateCheck
    exact ⟨rfl,rfl⟩
  obtain ⟨skipTrue,sameZ⟩ := checked
  subst z
  obtain ⟨funded,lastCredit⟩ := FinalDisposal.one_credit paid last
  have native : ((cleanup id pkt true).run v).run f=.ok (((),final),g) := by
    rwa [cleanup_poll_guard id pkt pid true owner]
  exact ⟨skipTrue,FinalDisposal.rx allocation _ funded lastCredit id pkt true key f g native⟩

/-- Timer selection, firing, clear work and the final receive disposal share
all intermediate worlds and clock records. Pending RX credit survives slot
and index unpublication until this actual native last-reference payment. -/
theorem final_dead_rx (trace : Runner.Trace) (placeholders : Bool)
    (initialized : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (device : w.wg.dev=some deviceState) (bound : UInt64) (pid : PeerId)
    (entry : WheelEntry) (due : TimerWheel.nextDue deviceState bound=some (pid,.zeroKeyMaterial,entry))
    (published : ∀p,deviceState.peers[pid]?=some p→HasKeySlot p)
    (kind : Worker) (prior : Option UInt64)
    (fired : (timerDispatchUnit kind pid .zeroKeyMaterial entry prior).run w=.ok ((),u))
    (p : Peer) (found : peerAt u.wg pid=some p) (a : Ambient)
    (cleared : ((runFlushedClearWork pid).run u.wg).run u.ambient=.ok (((),clearedWorld),a))
    (allocation : Credits.Allocation) (old : allocation.slot∈Unpublication.SlotEntries p)
    (projected : durableLoans clearedWorld=some loans) (last : (loans.map (·.allocation)).count allocation=1)
    (receiver id : Nat) (pkt : RxPacket) (owner : pkt.peer=receiver) (key : pkt.keypair=allocation.slot)
    (dead : pkt.state=.dead) (b c d e f g : Ambient)
    (peek : ((peekRxQueue receiver).run clearedWorld).run a=.ok ((some id,peekedWorld),b))
    (test : ((NativeRxSelection.ready (some id)).run peekedWorld).run b=.ok ((true,testedWorld),c))
    (read : ((getRxSkb id).run testedWorld).run c=.ok ((pkt,readWorld),d))
    (drop : ((dropRxQueue receiver).run readWorld).run d=.ok (((),droppedWorld),e))
    (stateCheck : ((branch .rxPollNotCrypted (pkt.state != .crypted) : WG.M Bool).run droppedWorld).run e=
      .ok ((skip,checkedWorld),f))
    (dispose : ((do
      keypairPut (some pkt.keypair) false
      peerPut (some receiver)
      _←branch .rxPollFree true
      freeRxSkb id : WG.M Unit).run checkedWorld).run f=.ok (((),final),g)) :
    HolderAccount [] clearedWorld ∧ SlotsCleared pid clearedWorld ∧ Unpublished allocation.slot clearedWorld ∧
      skip=true ∧ keyAt final allocation.slot=none := by
  have retired := selected trace placeholders initialized deviceState device bound pid entry due published
    kind prior fired p found a cleared
  have disposed := dead_rx retired.2.1 allocation projected last receiver id pkt owner key dead
    a b c d e f g peek test read drop stateCheck dispose
  exact ⟨retired.2.1,retired.2.2.1,retired.2.2.2.1 allocation.slot old,disposed⟩

end Leanux.Proofs.WG.RetirementSecurity.ConditionalRetirement
