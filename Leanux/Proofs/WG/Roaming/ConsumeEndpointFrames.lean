import Leanux.Proofs.WG.Roaming.ResponseRejectionFrames
import Leanux.Proofs.WG.Config.QueuedReferenceSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

private theorem consumeEndpoint_write (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]? = some p) (endpoint : q.endpoint = p.endpoint) :
    responseEndpointMap (some (Config.withPeer d pid q)) = responseEndpointMap (some d) := by
  funext other
  by_cases same : pid = other
  · subst other; simp [responseEndpointMap,Config.withPeer,resident,endpoint]
  · simp [responseEndpointMap,Config.withPeer,Std.TreeMap.getElem?_insert,same]

/-- Endpoint-map variant of C1 WGMore.enqueuePerDeviceAndPeerRx_spec.
Every normal enqueue outcome preserves optional endpoints, including full-queue
and full-ring refusals; no queue coherence or peer readiness is assumed. -/
theorem enqueuePerDeviceAndPeerRx_spec_endpoints_variant (id : SkbId) (entry : Option Device) :
    Ensures (enqueuePerDeviceAndPeerRx id)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  let safe : WGWorld → Prop := fun g => responseEndpointMap g.dev = responseEndpointMap entry
  change Ensures _ safe (fun _ => safe)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) safe (fun _ => safe) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) safe (fun _ => safe) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) safe)
  have hdev : Ensures getDev safe (fun _ => safe) := by
    intro g a r final after pre run
    cases hd : g.dev with
    | none => simp [getDev,hd,invariant,AmbientM.invariant] at run; cases run
    | some old => simp [getDev,hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hskb {α : Type} (action : SkbM α) : Ensures (liftSkb action) safe (fun _ => safe) := by
    intro g a r final after pre run
    cases device : g.dev with
    | none => simp [liftSkb,getDev,device,invariant,AmbientM.invariant] at run; cases run
    | some d =>
      cases executed : (action.run {txSkbs := d.txSkbs,rxSkbs := d.rxSkbs,nextSkb := d.nextSkb}).run a with
      | error stop => simp [liftSkb,getDev,device,executed] at run; cases run
      | ok pair =>
        obtain ⟨⟨value,store⟩,inputs⟩ := pair
        simp [liftSkb,getDev,modifyDev,device,executed] at run
        rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
        change responseEndpointMap (some d) = responseEndpointMap entry
        simpa only [safe,device] using pre
  have hmodify (f : Device → Device) (same : ∀ d, (f d).peers = d.peers) :
      Ensures (modifyDev f) safe (fun _ => safe) := by
    intro g a r final after pre run
    cases run
    have unchanged : responseEndpointMap (g.dev.map f) = responseEndpointMap g.dev := by
      funext pid
      cases device : g.dev <;> simp [responseEndpointMap,same]
    exact unchanged.trans pre
  have hcpu (last : Int) : Ensures (cpumaskNextOnlineFrom last) safe (fun _ => safe) := by
    unfold cpumaskNextOnlineFrom
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro wrap
    cases wrap <;> exact hpure _
  have hqueue : Ensures (queueDeviceWork .decryptWorker : WG.M Unit) safe (fun _ => safe) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.queueDeviceWork .decryptWorker) safe)
  have hset (pid : PeerId) (p : Peer) :
      Ensures (setPeer pid {p with rxQueue := p.rxQueue.enqueue id})
        (fun g => safe g ∧ peerAt g pid = some p) (fun _ => safe) := by
    intro g a r final after pre run
    cases run
    cases device : g.dev with
    | none => simp [peerAt,device] at pre
    | some d =>
      have resident : d.peers[pid]? = some p := by simpa [peerAt,device] using pre.2
      change safe {g with dev := g.dev.map (fun d => {d with peers := d.peers.insert pid {p with rxQueue := p.rxQueue.enqueue id}})}
      simp only [safe,device,Option.map_some]
      exact (consumeEndpoint_write d pid p {p with rxQueue := p.rxQueue.enqueue id} resident rfl).trans (by simpa [safe,device] using pre.1)
  have hrest : Ensures (do
      let old ← getDev
      let cpu ← cpumaskNextOnlineFrom old.decryptLastCpu
      modifyDev fun d => {d with decryptLastCpu := cpu}
      if ← branch .enqueueRingFull old.decryptQueue.full then return -EPIPE
      queueDeviceWork .decryptWorker
      modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id}
      return (0 : Int)) safe (fun _ => safe) := by
    repeat' first
      | with_reducible exact hpure _
      | with_reducible exact hbranch _ _
      | with_reducible exact hdev
      | with_reducible exact hcpu _
      | with_reducible exact hqueue
      | with_reducible exact hmodify _ (fun _ => rfl)
      | (with_reducible refine ensures_bind (Q := fun _ => safe) _ _ ?_ (fun _ => ?_))
      | split
      | simp only [bind_assoc,pure_bind]
  unfold enqueuePerDeviceAndPeerRx
  refine ensures_bind _ _ (hskb _) ?_
  intro _
  refine ensures_bind _ _ (hskb _) ?_
  intro pkt
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pkt.peer safe)) ?_
  intro p
  refine ensures_bind (Q := fun _ g => safe g ∧ peerAt g pkt.peer = some p) _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch .enqueuePeerQueueFull _) _)) ?_
  intro full
  cases full with
  | true => intro g a r final after pre run; cases run; exact pre.1
  | false => exact ensures_bind _ _ (hset pkt.peer p) (fun _ => hrest)

/-- Endpoint-map variant of C1 WGMore.enqueuePerPeerRx_pure_spec. The actual
acquire supplies the reference for the matching release. The callback here is
exactly the pure callback used by consumeData's EPIPE branch. -/
theorem enqueuePerPeerRx_pure_spec_endpoints_variant (id : SkbId) (state : PacketState)
    (entry : Option Device) :
    Ensures (enqueuePerPeerRx (pure () : WG.M Unit) id state)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  let safe : WGWorld → Prop := fun g => responseEndpointMap g.dev = responseEndpointMap entry
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) safe (fun _ => safe) := by
    intro g a r final after pre run; cases run; exact pre
  have hstop {α : Type} (message : String) : Ensures (invariant message : WG.M α) safe (fun _ => safe) := by
    intro g a r final after pre run; cases run
  have hdev : Ensures getDev safe (fun _ => safe) := by
    intro g a r final after pre run
    cases hd : g.dev with
    | none => simp [getDev,hd,invariant,AmbientM.invariant] at run; cases run
    | some old => simp [getDev,hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hkey (key : KeypairId) : Ensures (getKeypair key) safe (fun _ => safe) := by
    unfold getKeypair
    refine ensures_bind _ _ hdev ?_
    intro old
    split
    · exact hpure _
    · exact hstop _
  have hword (key : KeypairId) : Ensures (IndexOwner.peerDeref (.keypair key)) safe (fun _ => safe) := by
    simp only [IndexOwner.peerDeref,IndexOwner.peerWord,bind_assoc,pure_bind]
    refine ensures_bind _ _ (hkey key) ?_
    intro k
    cases k.peer with
    | none => exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.unsupported _) safe)
    | some pid => exact hpure _
  have hskb {α : Type} (action : SkbM α) (P : WGWorld → Prop)
      (stable : ∀ g d (store : SkbStore), P g → g.dev = some d →
        P {g with dev := some {d with txSkbs := store.txSkbs,rxSkbs := store.rxSkbs,nextSkb := store.nextSkb}}) :
      Ensures (liftSkb action) P (fun _ => P) := by
    intro g a r final after pre run
    cases device : g.dev with
    | none => simp [liftSkb,getDev,device,invariant,AmbientM.invariant] at run; cases run
    | some d =>
      cases executed : (action.run {txSkbs := d.txSkbs,rxSkbs := d.rxSkbs,nextSkb := d.nextSkb}).run a with
      | error stop => simp [liftSkb,getDev,device,executed] at run; cases run
      | ok pair =>
        obtain ⟨⟨value,store⟩,inputs⟩ := pair
        simp [liftSkb,getDev,modifyDev,device,executed] at run
        rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
        exact stable g d store pre device
  let tail (pid : PeerId) : WG.M Unit := do
    let p ← getPeer pid
    if !(p.rxQueue.all.contains id) then invariant "a decrypted packet that is not on its peer's rx_queue"
    setRxSkb id fun q => {q with state}
    setPeer pid {p with napiScheduled := true}
    pure ()
    peerPut (some pid)
  have htail (pid : PeerId) : Ensures (tail pid) (ResponseEndpointHeld entry pid) (fun _ => safe) := by
    have hsetRx (p : Peer) : Ensures (setRxSkb id fun q => {q with state})
        (fun g => ResponseEndpointHeld entry pid g ∧ peerAt g pid = some p)
        (fun _ g => ResponseEndpointHeld entry pid g ∧ peerAt g pid = some p) := by
      apply hskb
      intro g d store pre device
      obtain ⟨⟨same,old,q,present,resident,held⟩,readPeer⟩ := pre
      rw [device] at present
      cases present
      refine ⟨⟨?_,_,q,rfl,resident,held⟩,?_⟩
      · change responseEndpointMap (some d) = responseEndpointMap entry
        simpa only [device] using same
      · simpa only [peerAt,device,Option.bind_some] using readPeer
    have hset (p : Peer) : Ensures (setPeer pid {p with napiScheduled := true})
        (fun g => ResponseEndpointHeld entry pid g ∧ peerAt g pid = some p)
        (fun _ => ResponseEndpointHeld entry pid) := by
      intro g a r final after pre run
      obtain ⟨⟨same,d,q,device,resident,held⟩,readPeer⟩ := pre
      have equal : q = p := by simpa [peerAt,device,resident] using readPeer
      subst q
      cases run
      refine ⟨?_,Config.withPeer d pid {p with napiScheduled := true},{p with napiScheduled := true},?_,?_,held⟩
      · change responseEndpointMap (g.dev.map _) = _
        rw [device]
        exact (consumeEndpoint_write d pid p {p with napiScheduled := true} resident rfl).trans (by simpa [device] using same)
      · simp [device,Config.withPeer]
      · simp [Config.withPeer]
    unfold tail
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid (ResponseEndpointHeld entry pid))) ?_
    intro p
    split
    · intro g a r final after pre run; cases run
    · refine ensures_bind _ _ (hsetRx p) ?_
      intro _
      exact ensures_bind _ _ (hset p) (fun _ => peerPut_responseEndpoints entry pid)
  have hpublish (pid : PeerId) : Ensures (do peerGet pid; tail pid) safe (fun _ => safe) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [peerGet,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run; cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none => simp [peerGet,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run; cases run
      | some p =>
        have composed : Ensures (do peerGet pid; tail pid) (fun g => g.dev = some d) (fun _ => safe) := by
          refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (Config.peerGet_exact pid d p resident)) ?_
          intro _ middle inputs out finish tailInputs acquired runTail
          apply htail pid middle inputs out finish tailInputs ?_ runTail
          refine ⟨?_,Config.withPeer d pid {p with refcount := p.refcount + 1},
            {p with refcount := p.refcount + 1},acquired.1,?_,by change 1 < p.refcount + 1; omega⟩
          · rw [acquired.1]
            exact (consumeEndpoint_write d pid p {p with refcount := p.refcount + 1} resident rfl).trans (by simpa [safe,device] using pre)
          · simp [Config.withPeer]
        exact composed g ambient result final after device run
  change Ensures (do
    let pkt ← getRxSkb id
    let pid ← IndexOwner.peerDeref (.keypair pkt.keypair)
    peerGet pid
    tail pid) safe (fun _ => safe)
  refine ensures_bind _ _ (hskb _ safe (by
    intro g d store pre device
    change responseEndpointMap (some d) = responseEndpointMap entry
    simpa only [safe,device] using pre)) ?_
  intro pkt
  exact ensures_bind _ _ (hword pkt.keypair) hpublish

end Leanux.Proofs.WG.Roaming
