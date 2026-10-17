import Leanux.Proofs.WG.TimerDiscipline.SendCutFrames
import Leanux.Proofs.WG.TimerDiscipline.SendView
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def sendKernel (k : WGWorld) (pid : PeerId) : SendView :=
  (k.dev.map tableCursor, (k.dev.bind fun d => d.peers[pid]?).map initiationView)

def sendAt (w : WGWorld) (pid : PeerId) : SendView := sendKernel w pid

theorem sendAt_observation (w : WGWorld) (ambient : Ambient) (pid : PeerId) :
    sendAt w pid = sendObservation (Campaign2.snapshot w ambient) pid := rfl

/-- Forget only the additional table/cursor observation of a send frame. -/
theorem initiation_frame_of_send {α : Type} (action : Leanux.M α) (pid : PeerId)
    (frame : ∀ (q : Option TableCursor) (v : Option InitiationView),
      ⦃fun w => ⌜sendAt w.wg pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendAt w.wg pid = (q, v)⌝⦄) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w.wg pid = some v⌝⦄ action
      ⦃⇓? _ w => ⌜initiationAt w.wg pid = some v⌝⦄ := by
  apply (Product.ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (Product.ensures_iff _ _ _).mpr (frame (sendAt w.wg pid).1 (some v)) w result final
    (by simpa [sendAt, sendKernel, initiationAt, peerAt] using pre) run
  exact congrArg Prod.snd h

theorem initiation_frame_of_send_native {α : Type} (action : WG.M α) (pid : PeerId)
    (frame : ∀ (q : Option TableCursor) (v : Option InitiationView),
      ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ action
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  have h := (ensures_iff _ _ _).mpr (frame (sendAt w pid).1 (some v)) w ambient result final after
    (by simpa [sendAt, sendKernel, initiationAt, peerAt] using pre) run
  exact congrArg Prod.snd h

def sendWorkKernel (k : WGWorld) (pid : PeerId) : SendWorkView :=
  (k.dev.map sendWorkDevice, (k.dev.bind fun d => d.peers[pid]?).map sendWorkPeer)

def sendWorkAt (w : WGWorld) (pid : PeerId) : SendWorkView := sendWorkKernel w pid

def workKernel (k : WGWorld) (pid : PeerId) : WorkView :=
  (k.dev.map Device.sendWorkQueue, (k.dev.bind fun d => d.peers[pid]?).map Peer.handshakePending)

def workAt (w : WGWorld) (pid : PeerId) : WorkView := workKernel w pid

def queueWorkKernel (k : WGWorld) (pid : PeerId) : QueueWorkView :=
  (k.dev.map workQueues, (k.dev.bind fun d => d.peers[pid]?).map Peer.handshakePending)

def queueWorkAt (w : WGWorld) (pid : PeerId) : QueueWorkView := queueWorkKernel w pid

theorem workAt_observation (w : WGWorld) (ambient : Ambient) (pid : PeerId) :
    workAt w pid = workObservation (Campaign2.snapshot w ambient) pid := rfl

abbrev tunnelXmit := noise_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit

/-- Existing send interfaces forget only the added work-state fields. -/
theorem send_frame_of_sendWork {α : Type} (action : Leanux.M α) (pid : PeerId)
    (frame : ∀ (q : Option SendWorkDevice) (v : Option SendWorkPeer),
      ⦃fun w => ⌜sendWorkAt w.wg pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendWorkAt w.wg pid = (q, v)⌝⦄)
    (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w.wg pid = (q, v)⌝⦄ action
      ⦃⇓? _ w => ⌜sendAt w.wg pid = (q, v)⌝⦄ := by
  apply (Product.ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (Product.ensures_iff _ _ _).mpr
    (frame (sendWorkAt w.wg pid).1 (sendWorkAt w.wg pid).2) w result final rfl run
  have projected := congrArg (fun x : SendWorkView =>
    (x.1.map Prod.fst, x.2.map Prod.fst)) h
  have same : sendAt final.wg pid = sendAt w.wg pid := by
    simpa [sendAt, sendKernel, sendWorkAt, sendWorkKernel, sendWorkDevice, workQueues,
      sendWorkPeer, Option.map_map, Function.comp_def] using projected
  exact same.trans pre

theorem send_frame_of_sendWork_native {α : Type} (action : WG.M α) (pid : PeerId)
    (frame : ∀ (q : Option SendWorkDevice) (v : Option SendWorkPeer),
      ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄)
    (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ action
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  have h := (ensures_iff _ _ _).mpr
    (frame (sendWorkAt w pid).1 (sendWorkAt w pid).2) w ambient result final after rfl run
  have projected := congrArg (fun x : SendWorkView =>
    (x.1.map Prod.fst, x.2.map Prod.fst)) h
  have same : sendAt final pid = sendAt w pid := by
    simpa [sendAt, sendKernel, sendWorkAt, sendWorkKernel, sendWorkDevice, workQueues,
      sendWorkPeer, Option.map_map, Function.comp_def] using projected
  exact same.trans pre

theorem work_frame_of_sendWork {α : Type} (action : Leanux.M α) (pid : PeerId)
    (frame : ∀ (q : Option SendWorkDevice) (v : Option SendWorkPeer),
      ⦃fun w => ⌜sendWorkAt w.wg pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendWorkAt w.wg pid = (q, v)⌝⦄) (v : WorkView) :
    ⦃fun w => ⌜workAt w.wg pid = v⌝⦄ action
      ⦃⇓? _ w => ⌜workAt w.wg pid = v⌝⦄ := by
  apply (Product.ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (Product.ensures_iff _ _ _).mpr
    (frame (sendWorkAt w.wg pid).1 (sendWorkAt w.wg pid).2) w result final rfl run
  have projected := congrArg (fun x : SendWorkView =>
    (x.1.map (fun q => q.2.1), x.2.map Prod.snd)) h
  have same : workAt final.wg pid = workAt w.wg pid := by
    simpa [workAt, workKernel, sendWorkAt, sendWorkKernel, sendWorkDevice, workQueues,
      sendWorkPeer, Option.map_map, Function.comp_def] using projected
  exact same.trans pre

theorem queueWork_frame_of_sendWork {α : Type} (action : Leanux.M α) (pid : PeerId)
    (frame : ∀ (q : Option SendWorkDevice) (v : Option SendWorkPeer),
      ⦃fun w => ⌜sendWorkAt w.wg pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendWorkAt w.wg pid = (q, v)⌝⦄) (v : QueueWorkView) :
    ⦃fun w => ⌜queueWorkAt w.wg pid = v⌝⦄ action
      ⦃⇓? _ w => ⌜queueWorkAt w.wg pid = v⌝⦄ := by
  apply (Product.ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (Product.ensures_iff _ _ _).mpr
    (frame (sendWorkAt w.wg pid).1 (sendWorkAt w.wg pid).2) w result final rfl run
  have projected := congrArg (fun x : SendWorkView =>
    (x.1.map Prod.snd, x.2.map Prod.snd)) h
  have same : queueWorkAt final.wg pid = queueWorkAt w.wg pid := by
    simpa [queueWorkAt, queueWorkKernel, sendWorkAt, sendWorkKernel, sendWorkDevice,
      sendWorkPeer, Option.map_map, Function.comp_def] using projected
  exact same.trans pre

/-- Recover the old send-queue/pending interface from both queues in the same run. -/
theorem work_frame_of_queueWork {α : Type} (action : Leanux.M α) (pid : PeerId)
    (frame : ∀ (queues : WorkQueues) (pending : Bool),
      ⦃fun w => ⌜queueWorkAt w.wg pid = (some queues, some pending)⌝⦄ action
        ⦃⇓? _ w => ⌜queueWorkAt w.wg pid = (some queues, some pending)⌝⦄)
    (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w.wg pid = (some queue, some pending)⌝⦄ action
      ⦃⇓? _ w => ⌜workAt w.wg pid = (some queue, some pending)⌝⦄ := by
  apply (Product.ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.wg.dev with
  | none => simp [workAt, workKernel, hd] at pre
  | some d =>
    have hp : d.peers[pid]?.map Peer.handshakePending = some pending := by
      simpa [workAt, workKernel, hd] using congrArg Prod.snd pre
    have h := (Product.ensures_iff _ _ _).mpr
      (frame (workQueues d) pending) w result final
        (by simpa [queueWorkAt, queueWorkKernel, workAt, workKernel, hd] using hp) run
    have projected := congrArg (fun x : QueueWorkView => (x.1.map Prod.fst, x.2)) h
    have same : workAt final.wg pid = workAt w.wg pid := by
      simpa [queueWorkAt, queueWorkKernel, workAt, workKernel, workQueues,
        Option.map_map, Function.comp_def, hd, hp] using projected
    exact same.trans pre

theorem getPeer_sendWorkView (pid : PeerId) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ getPeer pid
      ⦃⇓? p w => ⌜some (sendWorkPeer p) = v ∧ sendWorkAt w pid = (q, v)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient p final after pre run
  obtain ⟨preserved, resident⟩ := (ensures_iff _ _ _).mpr
    (getPeer_spec pid (fun g => sendWorkAt g pid = (q, v))) g ambient p final after pre run
  have value := congrArg Prod.snd preserved
  change (peerAt final pid).map sendWorkPeer = v at value
  rw [resident] at value
  exact ⟨value, preserved⟩

theorem setPeer_sendWorkView (pid : PeerId) (q : Option SendWorkDevice) (v : Option SendWorkPeer) (p : Peer) :
    ⦃fun w => ⌜some (sendWorkPeer p) = v ∧ sendWorkAt w pid = (q, v)⌝⦄ setPeer pid p
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
    {d with peers := d.peers.insert pid p})}), ambient) = _ at run
  cases run
  rcases pre with ⟨value, before⟩
  cases device : g.dev with
  | none => simpa [sendWorkAt, sendWorkKernel, device] using before
  | some d =>
    simpa [sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, workQueues, device, value]
      using congrArg Prod.fst before

theorem dstCacheGet_sendWorkView (pid : PeerId) (gen : Nat) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ dstCacheGet pid gen
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  let P : WGWorld → Prop := fun g => sendWorkAt g pid = (q, v)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient y final after pre run; cases run; exact pre
  have hget : Ensures (get : WG.M WGWorld) P (fun _ => P) := by
    intro g ambient y final after pre run; cases run; exact pre
  have hmiss (p : Peer) :
      Ensures (do
        let ts ← hiddenJiffies .dstCacheRefreshTs
        setPeer pid {p with dstCache := {p.dstCache with slot := none, refreshTs := ts}}
        pure (none : Option DstSlot) : WG.M (Option DstSlot))
        (fun g => some (sendWorkPeer p) = v ∧ P g) (fun _ => P) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.hiddenJiffies .dstCacheRefreshTs)
        (fun g => some (sendWorkPeer p) = v ∧ P g))) ?_
    intro ts
    refine ensures_bind _ _ ?_ (fun _ => hpure none)
    exact (ensures_iff _ _ _).mpr (setPeer_sendWorkView pid q v _)
  apply (ensures_iff _ _ _).mp
  unfold dstCacheGet
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (get : AmbientM Ambient) P)) ?_
  intro inputs
  refine ensures_bind _ _ hget ?_
  intro state
  split
  · exact hpure none
  · refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_sendWorkView pid q v)) ?_
    intro p
    cases slot : p.dstCache.slot with
    | none => simpa only [slot] using hmiss p
    | some slotValue =>
      simp only [slot]
      split
      · intro g ambient result final after pre run
        cases run
        exact pre.2
      · exact hmiss p

theorem dstCacheSet_sendWorkView (pid : PeerId) (src gen dev : Nat) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ dstCacheSet pid src gen dev
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold dstCacheSet
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_sendWorkView pid q v)) ?_
  intro p g ambient result final after pre run
  exact (ensures_iff _ _ _).mpr (setPeer_sendWorkView pid q v
    {p with dstCache := {p.dstCache with slot := some {src, gen, dev}}})
    g ambient result final after ⟨pre.1, pre.2⟩ run

theorem dstCacheReset_sendWorkView (pid : PeerId) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ dstCacheReset pid
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  let P : WGWorld → Prop := fun g => sendWorkAt g pid = (q, v)
  have hpure : Ensures (pure () : WG.M Unit) P (fun _ => P) := by
    intro g ambient y final after pre run; cases run; exact pre
  have hget : Ensures (get : WG.M WGWorld) P (fun _ => P) := by
    intro g ambient y final after pre run; cases run; exact pre
  apply (ensures_iff _ _ _).mp
  unfold dstCacheReset
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (get : AmbientM Ambient) P)) ?_
  intro inputs
  refine ensures_bind _ _ hget ?_
  intro state
  split
  · exact hpure
  · refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.hiddenJiffies .dstCacheResetTs) P)) ?_
    intro ts
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_sendWorkView pid q v)) ?_
    intro p
    exact (ensures_iff _ _ _).mpr (setPeer_sendWorkView pid q v _)

theorem tunnelXmit_sendWorkView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (r : Route) (exactRx : Bool) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ tunnelXmit e bytes ds r exactRx
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  let P : WGWorld → Prop := fun g => sendWorkAt g pid = (q, v)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient y final after pre run; cases run; exact pre
  have hgetdev : Ensures getDev P (fun _ => P) := by
    intro g ambient d final after pre run
    cases device : g.dev with
    | none =>
      simp [getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hport : Ensures (socketPort e.family) P (fun _ => P) := by
    unfold socketPort
    refine ensures_bind _ _ hgetdev ?_
    intro d
    split
    · exact hpure _
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
        (AmbientM.unsupported "a send while wg0's socket is NULL (-ENONET)") P)
  have hstats : Ensures (modifyDev fun d => {d with
      txPackets := d.txPackets + 1, txBytes := d.txBytes + bytes.length}) P (fun _ => P) := by
    intro g ambient y final after pre run
    cases run
    cases device : g.dev <;>
      simpa [P, sendWorkAt, sendWorkKernel, sendWorkDevice, tableCursor, workQueues, device] using pre
  have hsent (sport : Nat) :
      Ensures (modify fun g : WGWorld => {g with sent := g.sent ++ [{
        family := e.family, addr := e.addr, port := e.port, bytes, ds, sport, src := r.src}]}) P (fun _ => P) := by
    intro g ambient y final after pre run
    cases run
    exact pre
  let rest : WG.M Unit := do
    if exactRx then loopbackSend ([.ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts) true
    else skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx]
    modifyDev fun d => {d with txPackets := d.txPackets + 1, txBytes := d.txBytes + bytes.length}
    let sport ← socketPort e.family
    modify fun g => {g with sent := g.sent ++ [{family := e.family, addr := e.addr, port := e.port, bytes, ds, sport, src := r.src}]}
  have restFrame : Ensures rest P (fun _ => P) := by
    unfold rest
    cases exactRx with
    | false =>
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
        (AmbientM.skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx]) P)) ?_
      intro _
      refine ensures_bind _ _ hstats ?_
      intro _
      refine ensures_bind _ _ hport ?_
      intro sport
      exact hsent sport
    | true =>
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (loopbackSend_spec_wg_variant P _ true)) ?_
      intro _
      refine ensures_bind _ _ hstats ?_
      intro _
      refine ensures_bind _ _ hport ?_
      intro sport
      exact hsent sport
  apply (ensures_iff _ _ _).mp
  change Ensures (if r.dev == WG0_IFINDEX then do
    unsupported "a datagram routed back into wg0"
    rest
    else rest) P (fun _ => P)
  split
  · intro g ambient result final after pre run
    simp [unsupported, AmbientM.unsupported] at run
    cases run
  · exact restFrame

theorem getPeer_sendView (pid : PeerId) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ getPeer pid
      ⦃⇓? p w => ⌜some (initiationView p) = v ∧ sendAt w pid = (q, v)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient p final after pre run
  obtain ⟨preserved, resident⟩ := (ensures_iff _ _ _).mpr
    (getPeer_spec pid (fun g => sendAt g pid = (q, v))) g ambient p final after pre run
  have value := congrArg Prod.snd preserved
  change (peerAt final pid).map initiationView = v at value
  rw [resident] at value
  exact ⟨value, preserved⟩

theorem setPeer_sendView (pid : PeerId) (q : Option TableCursor) (v : Option InitiationView) (p : Peer) :
    ⦃fun w => ⌜some (initiationView p) = v ∧ sendAt w pid = (q, v)⌝⦄ setPeer pid p
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
    {d with peers := d.peers.insert pid p})}), ambient) = _ at run
  cases run
  rcases pre with ⟨value, before⟩
  cases device : g.dev with
  | none => simpa [sendAt, sendKernel, device] using before
  | some d =>
    simpa [sendAt, sendKernel, tableCursor, device, value] using congrArg Prod.fst before

theorem dstCacheGet_sendView (pid : PeerId) (gen : Nat) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ dstCacheGet pid gen
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork_native (dstCacheGet pid gen) pid (dstCacheGet_sendWorkView pid gen) q v

theorem dstCacheSet_sendView (pid : PeerId) (src gen dev : Nat) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ dstCacheSet pid src gen dev
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork_native (dstCacheSet pid src gen dev) pid (dstCacheSet_sendWorkView pid src gen dev) q v

theorem dstCacheReset_sendView (pid : PeerId) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ dstCacheReset pid
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork_native (dstCacheReset pid) pid (dstCacheReset_sendWorkView pid) q v

theorem tunnelXmit_sendView (pid : PeerId) (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ tunnelXmit e bytes ds r exactRx
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork_native (tunnelXmit e bytes ds r exactRx) pid (tunnelXmit_sendWorkView pid e bytes ds r exactRx) q v

theorem getPeer_initiationView (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ getPeer pid
      ⦃⇓ p w => ⌜initiationView p = v ∧ initiationAt w pid = some v⌝⦄ := by
  apply (Leanux.Proofs.WG.Config.returns_iff _ _ _).mp
  intro g ambient pre
  cases device : g.dev with
  | none => simp [initiationAt, peerAt, device] at pre
  | some d =>
    cases resident : d.peers[pid]? with
    | none => simp [initiationAt, peerAt, device, resident] at pre
    | some p =>
      have value : initiationView p = v := by
        simpa [initiationAt, peerAt, device, resident] using pre
      refine ⟨p, g, ambient, ?_, value, pre⟩
      simp [getPeer, getDev, device, resident]
      rfl

theorem setPeer_initiationView (pid : PeerId) (v : InitiationView) (p : Peer) :
    ⦃fun w => ⌜initiationView p = v ∧ initiationAt w pid = some v⌝⦄ setPeer pid p
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  have h := (ensures_iff _ _ _).mpr
    (setPeer_sendView pid (sendAt w pid).1 (some v) p) w ambient result final after
    (by simpa [sendAt, sendKernel, initiationAt, peerAt] using pre) run
  exact congrArg Prod.snd h

theorem dstCacheGet_initiationView (pid : PeerId) (gen : Nat) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ dstCacheGet pid gen
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send_native (dstCacheGet pid gen) pid (dstCacheGet_sendView pid gen) v

theorem dstCacheSet_initiationView (pid : PeerId) (src gen dev : Nat) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ dstCacheSet pid src gen dev
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send_native (dstCacheSet pid src gen dev) pid (dstCacheSet_sendView pid src gen dev) v

theorem dstCacheReset_initiationView (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ dstCacheReset pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send_native (dstCacheReset pid) pid (dstCacheReset_sendView pid) v

theorem tunnelXmit_initiationView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (r : Route) (exactRx : Bool) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ tunnelXmit e bytes ds r exactRx
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send_native (tunnelXmit e bytes ds r exactRx) pid (tunnelXmit_sendView pid e bytes ds r exactRx) v

end Leanux.Proofs.WG.TimerDiscipline
