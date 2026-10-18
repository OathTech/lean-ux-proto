import Leanux.Proofs.WG.Queues.CurrentSlotTraffic

/-! Actual receive-completion source composition for the three-slot invariant.
Timer records, peer deletion, routing lookup and staged-send failures are kept. -/
namespace Leanux.Proofs.WG.CurrentSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

private theorem place_preserves (pid : PeerId) (t : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) : Preserves Inv (placeOnWheel pid t expires clk unit) := by
  let R := fun (p : Peer) (w : WGWorld) =>
    Inv w ∧ Affiliation.peerAt w pid = some (Affiliation.peerCell p)
  have hg : Hoare (getPeer pid) Inv (fun p => R p) :=
    Affiliation.getPeer_spec (fun v => ∀ s, v = some s → SlotInv s) pid
  have peerRead : Preserves Inv (getPeer pid) :=
    hoare_consequence hg (fun _ h => h) (fun _ _ h => h.1)
  have setter (p q : Peer) (hc : Affiliation.peerCell q = Affiliation.peerCell p) :
      Hoare (setPeer pid q) (R p) (fun _ => Inv) := by
    apply hoare_consequence (Affiliation.setPeer_spec
      (fun v => ∀ s, v = some s → SlotInv s) pid q)
    · intro w h
      exact ⟨h.1,by simpa only [hc] using h.2⟩
    · exact fun _ _ h => h
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Preserves Q (monadLift a : WG.M α) := hoare_liftAmbient a Q
  have stopped {α : Type} (e : Stop) (Q : WGWorld → Prop) (T : α → WGWorld → Prop) :
      Hoare (throw e : WG.M α) Q T := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b _ hr
    cases hr
  have read (Q : WGWorld → Prop) : Preserves Q (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get Q) (fun _ h => h) (fun _ _ h => h.2)
  have finish : Preserves Inv (do
      let p ← getPeer pid
      if let some what := TimerWheel.peerWheelProblem p then
        invariant s!"peer {pid}'s timers: {what}") := by
    apply preserves_bind peerRead
    intro p
    cases TimerWheel.peerWheelProblem p with
    | none => exact preserves_pure _
    | some what => exact ambient (AmbientM.invariant _) Inv
  unfold placeOnWheel
  apply hoare_bind _ _ hg
  intro p
  cases TimerWheel.place p t expires clk with
  | kept entry =>
    apply hoare_bind _ _ (setter p (p.setTimer t (some expires)) (by cases t <;> rfl))
    intro _
    split
    · apply preserves_bind (ambient AmbientM.peekHiddenSite Inv)
      intro site
      split
      · exact stopped _ _ _
      · exact finish
    · exact finish
  | enqueued slot bexp =>
    let tail : WG.M Unit := do
      let lvl := TimerWheel.levelOf slot
      if !(timeAfter bexp expires && timeBeforeEq bexp (expires + (TimerWheel.LVL_GRAN lvl).toUInt64)) then
        invariant s!"a bucket expiry {bexp} outside (expires, expires + 8^{lvl}] for expires {expires}"
      let stamp := (← get).timerEnqueues + 1
      modify fun k => {k with timerEnqueues := stamp}
      setPeer pid ((p.setTimer t (some expires)).setWheel t (some ⟨slot,bexp,stamp⟩))
      let q ← getPeer pid
      if let some what := TimerWheel.peerWheelProblem q then
        invariant s!"peer {pid}'s timers: {what}"
    have ht : Hoare tail (R p) (fun _ => Inv) := by
      unfold tail
      dsimp only
      split
      · exact stopped _ _ _
      · apply hoare_bind _ _ (read (R p))
        intro w
        have edited : Preserves (R p)
            (modify (fun k : WGWorld => {k with timerEnqueues := w.timerEnqueues+1}) : WG.M Unit) := by
          apply hoare_modify
          exact fun _ h => h
        apply hoare_bind _ _ edited
        intro _
        apply hoare_bind _ _ (setter p
          ((p.setTimer t (some expires)).setWheel t (some ⟨slot,bexp,w.timerEnqueues+1⟩))
          (by cases t <;> rfl))
        intro _
        exact finish
    cases unit with
    | none => exact ht
    | some u =>
      apply hoare_bind _ _ (ambient (AmbientM.hidden .timerEnqueue) (R p))
      intro eb
      dsimp only
      split
      · exact stopped _ _ _
      · split
        · exact stopped _ _ _
        · exact ht

theorem armTimer_preserves (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64 := none) : Preserves Inv (armTimer pid timer delay jc) := by
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient,hidden,invariant,unsupported]
  repeat' first
    | rxstack_preserves_join
    | (rx_retention_head placeOnWheel; exact place_preserves _ _ _ _ _)
    | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
    | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a result v b hi hr
       cases hr)
    | slot_traffic_step

theorem delTimer_preserves (pid : PeerId) (timer : PeerTimer) :
    Preserves Inv (delTimer pid timer) := by
  cases timer <;> unfold delTimer <;> repeat' slot_traffic_step

theorem modPeerTimer_preserves (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves Inv (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp Inv)
    | (rx_retention_head armTimer; exact armTimer_preserves _ _ _ _)
    | slot_traffic_step

theorem timersHandshakeComplete_preserves (pid : PeerId) (site : HiddenSite) :
    Preserves Inv (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head delTimer; exact delTimer_preserves _ _)
    | slot_traffic_step

theorem timersTraversal_preserves (pid : PeerId) : Preserves Inv (timersTraversal pid) := by
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp]
  repeat' first
    | (rx_retention_head discard
       change Preserves Inv (modPeerTimer _ _ _ _ >>= fun _ => pure ())
       exact preserves_bind (modPeerTimer_preserves _ _ _ _) (fun _ => preserves_pure ()))
    | (rx_retention_head modPeerTimer; exact modPeerTimer_preserves _ _ _ _)
    | slot_traffic_step

theorem timersDataReceived_preserves (pid : PeerId) : Preserves Inv (timersDataReceived pid) := by
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head discard
       change Preserves Inv (modPeerTimer _ _ _ _ >>= fun _ => pure ())
       exact preserves_bind (modPeerTimer_preserves _ _ _ _) (fun _ => preserves_pure ()))
    | (rx_retention_head modPeerTimer; exact modPeerTimer_preserves _ _ _ _)
    | slot_traffic_step

theorem keepKeyFreshRx_preserves (pid : PeerId) : Preserves Inv (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact sendQueuedHandshakeInitiation_preserves _ _)
    | slot_traffic_step

private theorem endpoint_fields (pid : PeerId) (endpoint : Endpoint) :
    SameView fields (setPeerEndpoint pid endpoint) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold setPeerEndpoint endpointEq WG.andM
  simp (config := {zeta := false}) only [requireNotPending,branch,pure_bind]
  repeat' first
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_fields _).wp (fun s => s = initial))
    | slot_fields_step initial

private theorem lookupSrc_view (protocol : Nat) (bytes : List UInt8) :
    SameView Affiliation.view (lookupSrc protocol bytes) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w a result v b rfl hr
  change (wgStoreView v).dev.map Affiliation.state = (wgStoreView w).dev.map Affiliation.state
  cases result with
  | none => change wgStoreView v = wgStoreView w at borrowed; rw [borrowed]
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    simp only [hv,hd,Option.map_some]
    exact congrArg some (Affiliation.state_peer_same d pid p {p with refcount := p.refcount+1} hp rfl)

private theorem stats_fields (pid : PeerId) (len : Nat) : SameView fields (updateRxStats pid len) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold updateRxStats
  repeat' slot_fields_step initial

private theorem dishonest_preserves (why : Dishonest) : Preserves Inv (dishonest why) := by
  cases why <;> unfold dishonest <;> repeat' slot_traffic_step

/-- All native normal completion branches preserve the three-slot invariant,
including promotion, staged-send failures and nullable lookup payment. -/
theorem consumeDataDone_preserves (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves Inv (consumeDataDone pid pkt endpoint) := by
  unfold consumeDataDone WG.andM WG.orM timersAnyAuthenticatedPacketReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerEndpoint; exact fields_preserves (project := fun w => w) (endpoint_fields _ _))
    | (rx_retention_head receivedWithKeypair; exact receivedWithKeypair_preserves _ _)
    | (rx_retention_head sendStagedPackets; exact sendStagedPackets_preserves _)
    | (rx_retention_head keepKeyFreshRx; exact keepKeyFreshRx_preserves _)
    | (rx_retention_head timersHandshakeComplete; exact timersHandshakeComplete_preserves _ _)
    | (rx_retention_head delTimer; exact delTimer_preserves _ _)
    | (rx_retention_head timersTraversal; exact timersTraversal_preserves _)
    | (rx_retention_head timersDataReceived; exact timersDataReceived_preserves _)
    | (rx_retention_head updateRxStats; exact fields_preserves (project := fun w => w) (stats_fields _ _))
    | (rx_retention_head dishonest; exact dishonest_preserves _)
    | (rx_retention_head lookupSrc; exact view_preserves (project := fun w => w) (lookupSrc_view _ _))
    | (rx_retention_head inetEcnDecapsulate
       exact fields_preserves (project := fun w => w) ((inetEcnDecapsulate_sameWGStore _ _ _).of_factor
         (fun s : WGStoreView => fields {dev := s.dev}) fields (fun _ => rfl)))
    | slot_traffic_step

end Leanux.Proofs.WG.CurrentSlots
