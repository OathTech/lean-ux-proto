import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxEnqueueFrames

/-! The original ENOSPC discard and the complete enqueue/publication suffix
consume or retain the same allocation carrier. Successful returns are split
by the actual errno arm; no returned state is asserted for an interrupted call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem Phased.unpublished_selected {c : RxCredits.Carrier}
    (account : Phased holders (c :: carriers) loans w) (phase : c.phase = .unpublished) :
    Phased holders (RxCredits.selected c :: carriers) loans w := by
  refine ⟨⟨account.funded.aligned,inventory_selected account.funded.carriers.inventory,?_,
    selected_protected account.funded.carriers.funded (by simp [phase,Phase.charged]),
    account.funded.carriers.keys⟩,?_⟩
  · intro d pid p id device found
    simpa [List.filter_cons,RxCredits.selected,phase] using account.funded.carriers.queues d pid p id device found
  · intro owner
    simpa only [demand,charges_cons,RxCredits.selected,phase,Phase.charged] using account.upper owner

theorem Phased.rx_discard {c : RxCredits.Carrier}
    (account : Phased holders (c :: carriers) loans w) (phase : c.phase = .unpublished)
    (owner : pkt.peer = c.owner.slot) (a b : Ambient)
    (run : ((RxCredits.discard c.packet.slot pkt).run w).run a = .ok (((),v),b)) :
    Phased holders carriers loans v ∧ packetAt v c.packet = none := by
  simp only [RxCredits.discard,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,keys,ak,keyRun,u',paidWorld,ap,peerRun,freeRun⟩ := run
  cases u
  cases u'
  have keysAccount := account.key_put _ _ a ak keyRun
  have selectedAccount := keysAccount.unpublished_selected phase
  have paidAccount := selectedAccount.receive_payment rfl ak ap (by simpa only [RxCredits.selected,owner] using peerRun)
  exact paidAccount.free_rx ap b freeRun

theorem Phased.rx_finish {c : RxCredits.Carrier}
    (account : Phased holders (c :: carriers) loans w) (ctx : RxOrigin.Admission)
    (phase : c.phase = .unpublished) (slot : c.packet.slot = ctx.slot)
    (stored : packetAt w c.packet = some ctx.packet) (owner : ctx.packet.peer = c.owner.slot)
    (ambient ambient' : Ambient)
    (run : ((finishSource ctx).run w).run ambient = .ok (((),v),ambient')) :
    ∃ ret middle aa,
      ((enqueuePerDeviceAndPeerRx ctx.slot).run w).run ambient = .ok ((ret,middle),aa) ∧
      ((finishAfter ctx ret).run middle).run aa = .ok (((),v),ambient') ∧
      (ret = 0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
      (if ret = -ENOSPC then Phased holders carriers loans v ∧ packetAt v c.packet = none
       else Phased holders (enqueued c :: carriers) loans v) := by
  have whole := run
  rw [finish_factor] at run
  obtain ⟨ret,middle,aa,enqueue,finish⟩ := (by simpa only [MaterialOrigin.bind_ok_ambient] using run)
  obtain ⟨choices,after⟩ := account.rx_enqueue phase stored owner ambient aa (by simpa [slot] using enqueue)
  refine ⟨ret,middle,aa,enqueue,finish,choices,?_⟩
  rcases choices with rfl | rfl | rfl
  · have same : v = middle := by
      simp [finishAfter,WG.orM,branch,AmbientM.branch,EPIPE,StateT.run_bind,StateT.run_monadLift] at finish
      exact finish.1.symm
    simpa [ENOSPC,same] using after
  · have discardRun : ((RxCredits.discard c.packet.slot ctx.packet).run middle).run (enospcDecisions aa) =
        .ok (((),v),ambient') := by
      simpa [slot] using (finish_enospc ctx ambient aa enqueue).symm.trans whole
    have entry : Phased holders (c :: carriers) loans middle := by simpa using after
    simpa using entry.rx_discard phase owner (enospcDecisions aa) ambient' discardRun
  · simp only [finishAfter,MaterialOrigin.bind_ok_ambient] at finish
    obtain ⟨decision,z,az,branchRun,finish⟩ := finish
    change Except.ok ((true,middle),CounterWindow.record aa .dataEpipe true) =
      .ok ((decision,z),az) at branchRun
    cases branchRun
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at finish
    obtain ⟨u,published,ap,publish,tail⟩ := finish
    cases u
    have entry : Phased holders (enqueued c :: carriers) loans middle := by simpa [ENOSPC,EPIPE] using after
    have publication := entry.publication ctx.slot .dead (CounterWindow.record aa .dataEpipe true) ap publish
    have same : v = published := by
      simp [WG.orM,branch,AmbientM.branch,EPIPE,StateT.run_bind,StateT.run_monadLift] at tail
      exact tail.1.symm
    simpa [ENOSPC,EPIPE,same] using publication

theorem Phased.rx_finish_boundary {c : RxCredits.Carrier}
    (account : Phased holders (c :: carriers) loans w) (stable : StableRx carriers w)
    (ctx : RxOrigin.Admission) (phase : c.phase = .unpublished) (slot : c.packet.slot = ctx.slot)
    (stored : packetAt w c.packet = some ctx.packet) (owner : ctx.packet.peer = c.owner.slot)
    (state : ctx.packet.state = .uncrypted) (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (ambient ambient' : Ambient)
    (run : ((finishSource ctx).run w).run ambient = .ok (((),v),ambient')) :
    ∃ ret middle aa,
      ((enqueuePerDeviceAndPeerRx ctx.slot).run w).run ambient = .ok ((ret,middle),aa) ∧
      ((finishAfter ctx ret).run middle).run aa = .ok (((),v),ambient') ∧
      (ret = 0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
      (if ret = -ENOSPC then Account holders carriers loans v ∧ packetAt v c.packet = none
       else Account holders (enqueued c :: carriers) loans v) := by
  obtain ⟨ret,middle,aa,enqueue,finish,choices,after⟩ :=
    account.rx_finish ctx phase slot stored owner ambient ambient' run
  have ready := finishAfter_stable ctx stable account.funded.carriers phase slot stored owner state
    physical ambient aa ambient' enqueue finish
  refine ⟨ret,middle,aa,enqueue,finish,choices,?_⟩
  by_cases full : ret = -ENOSPC <;> simp only [full,ite_eq_left,ite_false] at after ready ⊢
  · exact ⟨after.1.boundary ready,after.2⟩
  · exact after.boundary ready

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
