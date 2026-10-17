import Leanux.Proofs.WG.Index.OwnerReferenceModel
import Leanux.Proofs.WG.Index.RxQueueFrames
import Leanux.Proofs.WG.Config.QueuedReferenceSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

theorem ownerReferences_peerWrite (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]? = some p)
    (word : q.handshakeEntryPeer = p.handshakeEntryPeer)
    (count : q.refcount = p.refcount) :
    ownerReferences {d with peers := d.peers.insert pid q} = ownerReferences d := by
  unfold ownerReferences
  refine Prod.ext rfl ?_
  refine Prod.ext rfl ?_
  funext other
  by_cases same : pid = other
  · subst other; simp [resident, word, count]
  · simp [Std.TreeMap.getElem?_insert, same]

theorem hoare_liftSkb_references_variant {α : Type} (action : SkbM α) (d : Device) :
    Ensures (liftSkb action) (referencesAt d) (fun _ => referencesAt d) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none => simp [liftSkb, getDev, device, invariant, AmbientM.invariant] at run; cases run
  | some old =>
    cases executed : (action.run {txSkbs := old.txSkbs, rxSkbs := old.rxSkbs, nextSkb := old.nextSkb}).run ambient with
    | error err => simp [liftSkb, getDev, device, executed] at run; cases run
    | ok pair =>
      obtain ⟨⟨value, store⟩, inputs⟩ := pair
      simp [liftSkb, getDev, modifyDev, device, executed] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      simpa [referencesAt, device, ownerReferences] using pre

theorem enqueuePerDeviceAndPeerRx_spec_references_variant (id : SkbId) (d : Device) :
    Ensures (enqueuePerDeviceAndPeerRx id) (referencesAt d) (fun _ => referencesAt d) := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (referencesAt d) (fun _ => referencesAt d) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) (referencesAt d) (fun _ => referencesAt d) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) (referencesAt d))
  have hdev : Ensures getDev (referencesAt d) (fun _ => referencesAt d) := by
    intro g a r final after pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some old => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hmodify (f : Device → Device) (same : ∀ old, ownerReferences (f old) = ownerReferences old) :
      Ensures (modifyDev f) (referencesAt d) (fun _ => referencesAt d) := by
    intro g a r final after pre run
    cases run
    simpa [referencesAt, Option.map_map, Function.comp_def, same] using pre
  have hcpu (last : Int) : Ensures (cpumaskNextOnlineFrom last) (referencesAt d) (fun _ => referencesAt d) := by
    unfold cpumaskNextOnlineFrom
    refine ensures_bind (Q := fun _ => referencesAt d) _ _ (hbranch _ _) ?_
    intro wrap
    cases wrap <;> exact hpure _
  have hqueue : Ensures (queueDeviceWork .decryptWorker : WG.M Unit) (referencesAt d) (fun _ => referencesAt d) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.queueDeviceWork .decryptWorker) (referencesAt d))
  have hset (pid : PeerId) (p : Peer) :
      Ensures (setPeer pid {p with rxQueue := p.rxQueue.enqueue id})
        (fun g => referencesAt d g ∧ peerAt g pid = some p) (fun _ => referencesAt d) := by
    intro g a r final after pre run
    cases run
    cases device : g.dev with
    | none => simp [peerAt, device] at pre
    | some old =>
      have resident : old.peers[pid]? = some p := by simpa [peerAt, device] using pre.2
      simp only [referencesAt, Option.map_map, Function.comp_def]
      rw [device]
      simp only [Option.map_some, Option.some.injEq]
      exact (ownerReferences_peerWrite old pid p {p with rxQueue := p.rxQueue.enqueue id} resident rfl rfl).trans
        (by simpa [referencesAt, device] using pre.1)
  have hrest : Ensures (do
      let old ← getDev
      let cpu ← cpumaskNextOnlineFrom old.decryptLastCpu
      modifyDev fun old => {old with decryptLastCpu := cpu}
      if ← branch .enqueueRingFull old.decryptQueue.full then return -EPIPE
      queueDeviceWork .decryptWorker
      modifyDev fun old => {old with decryptQueue := old.decryptQueue.produce id}
      return (0 : Int)) (referencesAt d) (fun _ => referencesAt d) := by
    repeat' first
      | with_reducible exact hpure _
      | with_reducible exact hbranch _ _
      | with_reducible exact hdev
      | with_reducible exact hcpu _
      | with_reducible exact hqueue
      | with_reducible exact hmodify _ (fun _ => rfl)
      | (with_reducible refine ensures_bind (Q := fun _ => referencesAt d) _ _ ?_ (fun _ => ?_))
      | split
      | simp only [bind_assoc, pure_bind]
  unfold enqueuePerDeviceAndPeerRx
  refine ensures_bind _ _ (hoare_liftSkb_references_variant _ d) ?_
  intro _
  refine ensures_bind _ _ (hoare_liftSkb_references_variant _ d) ?_
  intro pkt
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pkt.peer (referencesAt d))) ?_
  intro p
  refine ensures_bind (Q := fun _ g => referencesAt d g ∧ peerAt g pkt.peer = some p) _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch .enqueuePeerQueueFull _) _)) ?_
  intro full
  cases full with
  | true =>
    intro g a r final after pre run; cases run; exact pre.1
  | false => exact ensures_bind _ _ (hset pkt.peer p) (fun _ => hrest)


private theorem referencesAt_put_acquired (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) :
    Ensures (peerPut (some pid))
      (referencesAt (Config.withPeer d pid {p with refcount := p.refcount + 1}))
      (fun _ => referencesAt d) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none => simp [referencesAt, device] at pre
  | some current =>
    have same : ownerReferences current = ownerReferences (Config.withPeer d pid {p with refcount := p.refcount + 1}) := by
      simpa [referencesAt, device] using pre
    have currentPeer := congrFun (congrArg (fun x => x.2.2) same) pid
    change current.peers[pid]?.map (fun q => (q.handshakeEntryPeer, q.refcount)) = _ at currentPeer
    simp only [Config.withPeer, ownerReferences, Std.TreeMap.getElem?_insert_self, Option.map_some] at currentPeer
    cases found : current.peers[pid]? with
    | none => simp [found] at currentPeer
    | some q =>
      simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at currentPeer
      have retained : 1 < q.refcount := by omega
      have post := ((ensures_iff _ _ _).mpr (Config.peerPut_retained pid current q found retained))
        g ambient result final after device run
      simp only [referencesAt, post, Option.map_some, Option.some.injEq]
      have table : current.indexTable = d.indexTable := congrArg Prod.fst same
      have keys : current.keypairs = d.keypairs := congrArg (fun x => x.2.1) same
      unfold ownerReferences
      refine Prod.ext table (Prod.ext keys ?_)
      funext other
      by_cases alias : pid = other
      · subst other
        simp [Config.withPeer, resident, currentPeer.1, currentPeer.2]
      · have old := congrFun (congrArg (fun x => x.2.2) same) other
        simpa [Config.withPeer, ownerReferences, Std.TreeMap.getElem?_insert, alias] using old


theorem enqueuePerPeerRx_pure_spec_references_variant (id : SkbId) (state : PacketState) (d : Device) :
    Ensures (enqueuePerPeerRx (pure () : WG.M Unit) id state)
      (referencesAt d) (fun _ => referencesAt d) := by
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) (referencesAt d) (fun _ => referencesAt d) := by
    intro g a r final after pre run; cases run; exact pre
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) (referencesAt d) (fun _ => referencesAt d) := by
    intro g a r final after pre run; cases run
  have hdev : Ensures getDev (referencesAt d) (fun _ => referencesAt d) := by
    intro g a r final after pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some old => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hkey (key : KeypairId) : Ensures (getKeypair key) (referencesAt d) (fun _ => referencesAt d) := by
    unfold getKeypair
    refine ensures_bind _ _ hdev ?_
    intro old
    split
    · exact hpure _
    · exact hstop _
  have hword (key : KeypairId) : Ensures (IndexOwner.peerDeref (.keypair key)) (referencesAt d) (fun _ => referencesAt d) := by
    simp only [IndexOwner.peerDeref, IndexOwner.peerWord, bind_assoc, pure_bind]
    refine ensures_bind _ _ (hkey key) ?_
    intro k
    cases k.peer with
    | none => exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.unsupported _) (referencesAt d))
    | some pid => exact hpure _
  let tail (pid : PeerId) : WG.M Unit := do
    let p ← getPeer pid
    if !(p.rxQueue.all.contains id) then
      invariant "a decrypted packet that is not on its peer's rx_queue"
    setRxSkb id fun q => {q with state}
    setPeer pid {p with napiScheduled := true}
    pure ()
    peerPut (some pid)
  have htail (old : Device) (pid : PeerId) (p : Peer)
      (resident : old.peers[pid]? = some p) (live : 0 < p.refcount) :
      Ensures (tail pid)
        (referencesAt (Config.withPeer old pid {p with refcount := p.refcount + 1}))
        (fun _ => referencesAt old) := by
    let acquired := Config.withPeer old pid {p with refcount := p.refcount + 1}
    have hsetRx (q : Peer) :
        Ensures (setRxSkb id fun pkt => {pkt with state})
          (fun g => referencesAt acquired g ∧ peerAt g pid = some q)
          (fun _ g => referencesAt acquired g ∧ peerAt g pid = some q) := by
      intro g ambient result final after pre run
      cases device : g.dev with
      | none => simp [referencesAt, device] at pre
      | some current =>
        cases executed : ((SkbStore.setRx id fun pkt => {pkt with state}).run
            {txSkbs := current.txSkbs, rxSkbs := current.rxSkbs, nextSkb := current.nextSkb}).run ambient with
        | error err => simp [setRxSkb, liftSkb, getDev, device, executed] at run; cases run
        | ok pair =>
          obtain ⟨⟨value, store⟩, inputs⟩ := pair
          simp [setRxSkb, liftSkb, getDev, modifyDev, device, executed] at run
          rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
          simpa [referencesAt, peerAt, device, ownerReferences] using pre
    have hset (q : Peer) :
        Ensures (setPeer pid {q with napiScheduled := true})
          (fun g => referencesAt acquired g ∧ peerAt g pid = some q)
          (fun _ => referencesAt acquired) := by
      intro g a r final after pre run
      cases run
      cases device : g.dev with
      | none => simp [peerAt, device] at pre
      | some current =>
        have found : current.peers[pid]? = some q := by simpa [peerAt, device] using pre.2
        simp only [referencesAt, Option.map_map, Function.comp_def]
        rw [device]
        simp only [Option.map_some, Option.some.injEq]
        exact (ownerReferences_peerWrite current pid q {q with napiScheduled := true} found rfl rfl).trans
          (by simpa [referencesAt, device] using pre.1)
    simp only [tail]
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid (referencesAt acquired))) ?_
    intro q
    split
    · intro g a r final after pre run; cases run
    · refine ensures_bind _ _ (hsetRx q) ?_
      intro _
      exact ensures_bind _ _ (hset q) (fun _ => referencesAt_put_acquired old pid p resident live)
  have hpublish (pid : PeerId) :
      Ensures (do peerGet pid; tail pid) (referencesAt d) (fun _ => referencesAt d) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [peerGet, requireNotPending, getPeer, getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some old =>
      cases resident : old.peers[pid]? with
      | none => simp [peerGet, requireNotPending, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run; cases run
      | some p =>
        have composed : Ensures (do peerGet pid; tail pid) (fun g => g.dev = some old) (fun _ => referencesAt old) := by
          refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (Config.peerGet_exact pid old p resident)) ?_
          intro _ g a r finish inputs h runTail
          exact htail old pid p resident h.2 g a r finish inputs
            (by simp [referencesAt, h.1]) runTail
        have finalReferences := composed g ambient result final after device run
        have oldReferences : ownerReferences old = ownerReferences d := by simpa [referencesAt, device] using pre
        exact finalReferences.trans (congrArg some oldReferences)
  change Ensures (do
    let pkt ← getRxSkb id
    let pid ← IndexOwner.peerDeref (.keypair pkt.keypair)
    peerGet pid
    tail pid) (referencesAt d) (fun _ => referencesAt d)
  refine ensures_bind _ _ (hoare_liftSkb_references_variant _ d) ?_
  intro pkt
  exact ensures_bind _ _ (hword pkt.keypair) hpublish

end Leanux.Proofs.WG.Index
