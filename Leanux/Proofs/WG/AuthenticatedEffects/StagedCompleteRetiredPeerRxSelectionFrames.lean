import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxFrames

/-! The original RX queue drop selects one already charged carrier. Its
identity comes from the actual cached head and the existing complete ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem peer_update_balance {q : Peer} (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (stamp : q.internalId = p.internalId) (count : q.refcount = p.refcount) (owner : Owner) :
    balance {w with dev := some {d with peers := d.peers.insert pid q}} owner = balance w owner := by
  rcases owner with ⟨epoch,slot,allocation⟩
  simp only [balance_factor,peerView,viewBalance,device,Option.map_some,Option.bind_some]
  by_cases same : pid = slot <;> simp_all [Std.TreeMap.getElem?_insert]

theorem Upper.selected {c : RxCredits.Carrier}
    (upper : Upper holders (c :: carriers) loans w) (phase : c.phase = .queued) :
    Upper holders (RxCredits.selected c :: carriers) loans w := by
  intro owner
  simpa only [demand,charges_cons,RxCredits.selected,phase,Phase.charged] using upper owner

theorem Account.rx_select {id : SkbId} {pkt : RxPacket} (account : Account holders carriers loans w)
    (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (peek : p.rxQueue.peeked = some id) (stored : d.rxSkbs[id]? = some pkt)
    (ready : pkt.state ≠ .uncrypted) (a b : Ambient)
    (run : ((dropRxQueue pid).run w).run a = .ok (((),v),b)) :
    let c : RxCredits.Carrier := ⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩
    Phased holders (c :: remaining carriers [⟨d.ifindex,id⟩]) loans v ∧
      StableRx (remaining carriers [⟨d.ifindex,id⟩]) v := by
  let queued : RxCredits.Carrier := ⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩
  have member : queued ∈ carriers := queued_carrier account.funded.carriers device found peek
  have split := List.perm_cons_erase member
  have before := (account.upper.carriers_perm split).selected rfl
  have kept : Upper holders (selected queued :: carriers.erase queued) loans v := by
    have state : v = {w with dev := some {d with peers := d.peers.insert pid {p with rxQueue := p.rxQueue.dropPeeked}}} := by
      have actual := run
      simp [dropRxQueue,getPeer,getDev,setPeer,modifyDev,device,found] at actual
      exact actual.1.symm
    intro owner
    rw [state,peer_update_balance (q := {p with rxQueue := p.rxQueue.dropPeeked}) device found rfl rfl]
    exact before owner
  have upper := kept.carriers_perm (List.Perm.cons _
    (remaining_one_perm account.funded.carriers.inventory.distinct split).symm)
  have frame := (hoare_iff_run_ambient _ _ _).mp (drop_frame pid w)
    w a () v b (Frame.refl w) run
  exact ⟨⟨⟨account.funded.aligned.frame frame,
      drop_state account.funded.carriers device found peek a b run⟩,upper⟩,
    account.stable.drop_ready device found peek stored ready a b run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
