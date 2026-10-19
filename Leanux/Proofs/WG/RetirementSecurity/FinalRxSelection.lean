import Leanux.Proofs.WG.RetirementSecurity.NativeRxSelection

/-! Retirement through the original selected DEAD RX path. The initialized
holder census supplies the sole credit before native selection; the source
state comparison skips authenticated completion and enters literal cleanup.
The same intermediate worlds and ambient records join every actual call. -/
namespace Leanux.Proofs.WG.RetirementSecurity.FinalRxSelection
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

/-- Concrete selection and cleanup progress for an actual DEAD packet removes
its allocation when that queued RX occurrence held the last reference. The
incoming account is derived from initialized execution, not assumed at cleanup. -/
theorem initialized_dead (trace : Runner.Trace) (placeholders : Bool)
    (initialized : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (allocation : Credits.Allocation) (projected : durableLoans w.wg=some loans)
    (last : (loans.map (·.allocation)).count allocation=1)
    (pid id : Nat) (pkt : RxPacket) (owner : pkt.peer=pid) (key : pkt.keypair=allocation.slot)
    (dead : pkt.state=.dead) (b c d e f g : Ambient)
    (peek : ((peekRxQueue pid).run w.wg).run w.ambient=.ok ((some id,u),b))
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
  obtain ⟨_,_,_,_,_,wire⟩ := NativeRxSelection.initialized_selected trace placeholders initialized
    pid id pkt b c d e peek test read drop
  obtain ⟨actual,named,credits⟩ := HolderInitialized.account trace placeholders initialized
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

end Leanux.Proofs.WG.RetirementSecurity.FinalRxSelection
