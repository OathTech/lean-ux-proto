import Leanux.Proofs.WG.Queues.NapiFrames

/-! Stable receive boundaries compose exact ring/packet frames with independent
queue and NAPI-bit retention. Peer deletion is allowed by both survivor frames. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes

private theorem queue_back {w v : WGWorld} {d : Device} {p : Peer} {pid : PeerId} (hq : ResidentsRetained (rxQueues w) (rxQueues v))
    (hd : v.dev = some d) (hp : d.peers[pid]? = some p) :
    ∃ before old, w.dev = some before ∧ before.peers[pid]? = some old ∧ old.rxQueue = p.rxQueue := by
  have old := hq pid ⟨d.ifindex,p.internalId,p.rxQueue⟩
    (by simp only [rxQueues,rxMap,hd,Option.bind_some,hp,Option.map_some])
  obtain ⟨before,hbefore,hmap⟩ := Option.bind_eq_some_iff.mp old
  obtain ⟨peer,hpeer,fields⟩ := Option.map_eq_some_iff.mp hmap
  exact ⟨before,peer,hbefore,hpeer,congrArg RxQueueCell.queue fields⟩

/-- A surviving queue obtains its head-state fact from the same original RX
cell. No assumption about the old or new NAPI bit is needed for this fact. -/
theorem ColdHead.retains (hi : ColdHead pid w)
    (rx : rxView v = rxView w) (hq : ResidentsRetained (rxQueues w) (rxQueues v)) :
    ColdHead pid v := by
  intro d p id hd hp head
  obtain ⟨before,old,hbefore,hold,queue⟩ := queue_back hq hd hp
  obtain ⟨pkt,stored,state⟩ := hi before old id hbefore hold (queue ▸ head)
  have cells := congrFun (congrArg Prod.snd rx) id
  exact ⟨pkt,by simpa [rxView,hd,hbefore,stored] using cells,state⟩

/-- Cold-head restoration needs both the queue and NAPI-bit survivor facts.
Neither carrier funding nor a queue-only frame supplies the latter. -/
theorem StableRx.retains (hs : StableRx cs w)
    (ring : RxRing.nativeCell v = RxRing.nativeCell w) (rx : rxView v = rxView w)
    (queues : ResidentsRetained (rxQueues w) (rxQueues v))
    (bits : NapiFrames.Retained (NapiFrames.napiView w) v) : StableRx cs v := by
  have packets : ∀p,packetAt v p=packetAt w p := fun p => by
    have epoch := congrArg Prod.fst rx
    have slots := congrFun (congrArg Prod.snd rx) p.slot
    cases h₁:v.dev <;> cases h₂:w.dev <;> simp_all [rxView,packetAt]
  refine ⟨hs.queued,?_,?_⟩
  · intro d hd
    have old : ∃e,w.dev=some e ∧ e.ifindex=d.ifindex ∧ e.decryptQueue=d.decryptQueue := by
      cases hw:w.dev <;> simp_all [RxRing.nativeCell]
    obtain ⟨e,he,epoch,hq⟩ := old
    simpa [epoch,hq,uncrypted,packets] using hs.ring e he
  · intro d pid p id hd hp cold head
    obtain ⟨before,old,hbefore,hold,queue⟩ := queue_back queues hd hp
    have bit := bits pid p.napiScheduled
      (by simp only [NapiFrames.napiView,hd,Option.bind_some,hp,Option.map_some])
    have napi : old.napiScheduled = p.napiScheduled := by
      simpa only [NapiFrames.napiView,hbefore,Option.bind_some,hold,Option.map_some,Option.some.injEq] using bit
    obtain ⟨pkt,stored,state⟩ := hs.cold before pid old id hbefore hold (napi.trans cold) (queue ▸ head)
    have cells := congrFun (congrArg Prod.snd rx) id
    exact ⟨pkt,by simpa [rxView,hd,hbefore,stored] using cells,state⟩

theorem stable_consumeDataDone (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (hs : StableRx cs w) (a b : Ambient)
    (hr : ((consumeDataDone pid pkt endpoint).run w).run a = .ok ((result,v),b)) :
    StableRx cs v := by
  apply hs.retains
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (RxRing.consumeDataDone_cell pid pkt endpoint) w a result v b hr
  · have fields := (ProjectedAction.iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.done_geometry) pid pkt endpoint)
      w a result v b hr
    exact congrArg Prod.snd fields
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (consumeDataDone_rxQueues pid pkt endpoint) w a result v b hr
  · exact (hoare_iff_run_ambient _ _ _).mp
      (NapiFrames.consumeDataDone_preserves pid pkt endpoint (NapiFrames.napiView w))
      w a result v b (NapiFrames.refl w) hr

/-- The actual product Stack callback preserves the supplied stable ledger.
The already-required key compatibility supplies its existing TX handoff frame. -/
theorem stable_stack (packets : List (List UInt8)) (hs : StableRx cs w.wg)
    (hk : KeysCompatible w.wg)
    (hr : (packets.forM Leanux.Env.deliverInner).run w = .ok ((),v)) : StableRx cs v.wg := by
  apply hs.retains
  · exact (ProjectedAction.iff_run _ _ _).mp (RxRing.stackForM_cell packets) w () v hr
  · have out := (hoare_iff_run _ _ _).mp (stackForM_stack w.wg packets)
      w () v ⟨Transfer.refl w.wg,hk⟩ hr
    obtain ⟨delta,handoff⟩ := out.1
    exact handoff.rx
  · exact (ProjectedAction.iff_run _ _ _).mp (stackForM_rxQueues packets) w () v hr
  · exact (hoare_iff_run _ _ _).mp (NapiFrames.stack_preserves packets (NapiFrames.napiView w.wg))
      w () v (NapiFrames.refl w.wg) hr

end Leanux.Proofs.WG.Queues.RxCredits
