import Leanux.Proofs.WG.Queues.DumpSockets
import Leanux.Proofs.WG.Queues.ClearWorkDispatch
import Leanux.Proofs.WG.Queues.DecryptCarrier
import Leanux.Proofs.WG.Queues.PassiveHolders
import Leanux.Proofs.WG.Queues.RxStableFrames

/-! Timer work reservations are added only from the actual acquisition paths.
The clear callback's queue extension is combined with every existing holder. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderTimers
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

/-- The passive fields unaffected when a timer extends only clear work. -/
def clearPassive (w : WGWorld) :=
  ((w.dev.map Device.peerList).getD [],activeCursor w.nlSock7,activeCursor w.nlSock8)

structure ClearFrame (w v : WGWorld) : Prop where
  passive : clearPassive v = clearPassive w
  send : sendView v = sendView w
  tx : ∀ pid batches, handoffTxView v pid = some batches → handoffTxView w pid = some batches

theorem ClearFrame.refl (w : WGWorld) : ClearFrame w w := ⟨rfl,rfl,fun _ _ h => h⟩

theorem ClearFrame.trans (first : ClearFrame w u) (next : ClearFrame u v) : ClearFrame w v :=
  ⟨next.passive.trans first.passive,next.send.trans first.send,
    fun pid batches found => first.tx pid batches (next.tx pid batches found)⟩

theorem ClearFrame.of_frame (frame : Frame w v) : ClearFrame w v := by
  refine ⟨?_,frame.send,frame.tx⟩
  exact congrArg (fun p => (p.1,p.2.2.1,p.2.2.2)) frame.passive

private theorem clear_frame_rule (action : WG.M α)
    (frame : ∀ initial, Preserves (Frame initial) action) (initial : WGWorld) :
    Preserves (ClearFrame initial) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact hi.trans (ClearFrame.of_frame
    ((hoare_iff_run_ambient _ _ _).mp (frame w) w a x v b (Frame.refl w) run))

/-- Only the clear queue changes; actual peer acquisition and possible
coalescing repayment retain all surviving TX queues and the other holders. -/
theorem expiredZero_frame (pid : PeerId) (initial : WGWorld) :
    Preserves (ClearFrame initial) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (rx_retention_head peerGet; exact clear_frame_rule _ (dump_peerGet_frame _) initial)
    | (rx_retention_head peerPut; exact clear_frame_rule _ (HolderWorkFrames.peerPut_frame _) initial)
    | (rx_retention_head getPeer
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a p v b hi run
       exact (getPeer_normal _ w v p a b run).1 ▸ hi)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head modifyDev
       apply hoare_modify
       intro w hi
       refine ⟨?_,?_,?_⟩
       · simpa only [clearPassive,Option.map_map,Function.comp_def] using hi.passive
       · simpa only [sendView,Option.map_map,Function.comp_def] using hi.send
       · intro q batches found
         exact hi.tx q batches (by simpa only [handoffTxView,Option.bind_map,Function.comp_def] using found))
    | rx_retention_step

  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a d v b hi run
  have same : v = w := (DecryptCarrier.getDev_current a b run).1
  rw [same]
  exact hi

def addClear (h : DurableHolders) (added : Reservations) : DurableHolders :=
  {h with clear := h.clear ++ added}

theorem addClear_owners (h : DurableHolders) (added : Reservations) (loans : Reservations) :
    ((addClear h added).owners ++ loans).Perm (added ++ (h.owners ++ loans)) := by
  apply List.perm_iff_count.mpr
  intro o
  simp only [addClear,owners,List.count_append]
  omega

/-- Newly queued clear work is charged by the callback's actual peerGet.
A rejected/coalesced queue attempt returns no addition after the source put. -/
theorem expiredZero_funded (pid : PeerId) {h : DurableHolders}
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((expiredZeroKeyMaterial pid).run w).run a = .ok (((),v),b)) :
    ∃ added : Reservations,
      (added = [] ∨ ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧
        added = [⟨d.ifindex,pid,p.internalId⟩]) ∧
      (addClear h added).Funded cs loans v ∧ StableRx cs v := by
  obtain ⟨added,source,kept,queue⟩ := ClearWork.timer_normal ⟨hi.carriers,stable⟩ a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (expiredZero_frame pid w)
    w a () v b (ClearFrame.refl w) run
  have aligned : (addClear h added).Aligned v := by
    have base := congrArg Prod.fst frame.passive
    have cursor7 := congrArg (fun p => p.2.1) frame.passive
    have cursor8 := congrArg (fun p => p.2.2) frame.passive
    refine ⟨hi.aligned.base.trans base.symm,?_,?_,?_,
      hi.aligned.cursor7.trans cursor7.symm,hi.aligned.cursor8.trans cursor8.symm⟩
    · intro d hd
      have same := frame.send
      cases hw : w.dev with
      | none => simp [sendView,hd,hw] at same
      | some old =>
        have eq : d.sendWorkQueue = old.sendWorkQueue := by
          simpa only [sendView,hd,hw,Option.map_some,Option.some.injEq] using same
        exact eq.trans (hi.aligned.send old hw)
    · change (h.clear ++ added).map Owner.slot = _
      rw [List.map_append,hi.aligned.clear]
      cases hw : w.dev with
      | none =>
        have empty : added = [] := by
          rcases source with empty | ⟨d,p,hd,_,_⟩
          · exact empty
          · simp [hw] at hd
        have out : v.dev = none := by
          cases hv : v.dev with
          | none => rfl
          | some d => simp [ClearWork.queueView,hw,hv] at queue
        simp [out,empty]
      | some old =>
        cases hv : v.dev with
        | none => simp [ClearWork.queueView,hw,hv] at queue
        | some d =>
          have eq : d.clearWorkQueue = old.clearWorkQueue ++ added.map Owner.slot := by
            simpa [ClearWork.queueView,hw,hv] using congrArg (Option.map Prod.snd) queue
          simp [eq]
    · intro q batches found
      exact hi.aligned.tx q batches (frame.tx q batches found)
  exact ⟨added,source,⟨aligned,WorkReservations.carrier_loans_perm kept.1 (addClear_owners h added loans).symm⟩,kept.2⟩

/-- Queued handshake work carries its actual acquired-reference delta into the
complete holder account. The coalesced path repays that reference in source. -/
theorem sendQueued_funded (pid : PeerId) (retry : Bool) {h : DurableHolders}
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((sendQueuedHandshakeInitiation pid retry).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ (h.absorb delta).Funded cs loans v ∧ StableRx cs v := by
  have transfer := (Transfers.iff_run_ambient _).mp (sendQueued_transfers pid retry) w a () v b run
  have effect := (KeyEffects.iff_run_ambient _ _).mp
    (queued_keyEffect (allowed := NoPromotion) pid retry) w a () v b run
  have passive := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.PassiveHolders.«0».Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders.sendQueued_preserves)
      pid retry (passiveView w)) w a () v b rfl run
  obtain ⟨delta,step⟩ := transfer
  have keys : KeysCompatible v :=
    ⟨effect.rxCompatible step.rx hi.carriers.keys.1,
      effect.currentsCompatible hi.carriers.keys.2 (fun _ _ h => h.elim)⟩
  have initial : h.Funded cs (loans ++ []) w := by simpa using hi
  have funded : (h.absorb delta).Funded cs loans v := by
    simpa using initial.handoff step keys passive
  refine ⟨delta,step,funded,?_⟩
  apply stable.retains
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (RxRing.sendQueuedHandshakeInitiation_cell pid retry) w a () v b run
  · exact step.rx
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (sendQueuedHandshakeInitiation_rxQueues pid retry) w a () v b run
  · exact (hoare_iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.NapiFrames.«0».Leanux.Proofs.WG.Queues.NapiFrames.sendQueued_preserves)
        pid retry (NapiFrames.napiView w)) w a () v b (NapiFrames.refl w) run

private theorem fixed_rule {h : DurableHolders} {cs : Ledger} {loans : Reservations}
    (action : WG.M α)
    (frame : ∀ initial, Preserves (Frame initial) action)
    (keeps : ∀ cs loans, Preserves (ClearWork.Inv cs loans) action) :
    Preserves (fun w => h.Funded cs loans w ∧ StableRx cs w) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  have fields := (hoare_iff_run_ambient _ _ _).mp (frame w) w a x v b (Frame.refl w) run
  have post := (hoare_iff_run_ambient _ _ _).mp (keeps cs (h.owners ++ loans))
    w a x v b ⟨hi.1.carriers,hi.2⟩ run
  exact ⟨⟨hi.1.aligned.frame fields,post.1⟩,post.2⟩

private theorem modify_peer {h : DurableHolders} {cs : Ledger} {loans : Reservations}
    (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Preserves (fun w => h.Funded cs loans w ∧ StableRx cs w)
      (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply fixed_rule
  · intro initial
    apply (pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.read_bind)
    intro p saved
    apply (pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.set_saved)
    simpa only [tx] using saved
  · intro cs loans
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.RxClearWork.«0».Leanux.Proofs.WG.Queues.RxCredits.ClearWork.modify_peer)
      pid f stamp count rx napi current

/-- The actual endpoint/cache reset changes no durable charge or RX boundary.
Its hidden timestamp and all source failures remain part of the execution. -/
theorem clearEndpoint_preserves {h : DurableHolders} {cs : Ledger} {loans : Reservations}
    (pid : PeerId) :
    Preserves (fun w => h.Funded cs loans w ∧ StableRx cs w) (clearPeerEndpointSrc pid) := by
  have cacheWrite (ts : UInt64) : Preserves (fun w => h.Funded cs loans w ∧ StableRx cs w)
      (do let p ← getPeer pid; setPeer pid {p with dstCache := {p.dstCache with resetTs := ts}}) :=
    modify_peer pid (fun p => {p with dstCache := {p.dstCache with resetTs := ts}})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ hk => hk) (fun _ => rfl)
  have cache : Preserves (fun w => h.Funded cs loans w ∧ StableRx cs w) (dstCacheReset pid) := by
    unfold dstCacheReset
    simp only [getAmbient,hiddenJiffies]
    repeat' first
      | (env_bind_head getPeer; exact cacheWrite _)
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))
      | rx_retention_step
  have now : Preserves (fun w => h.Funded cs loans w ∧ StableRx cs w) (dstCacheResetNow pid) := by
    unfold dstCacheResetNow
    apply preserves_bind cache
    intro _
    exact modify_peer pid (fun p => {p with dstCache := {p.dstCache with slot := none}})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ _ hk => hk) (fun _ => rfl)
  unfold clearPeerEndpointSrc
  rw [← bind_assoc]
  apply preserves_bind (modify_peer pid
    (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0,srcIf := 0}})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ hk => hk) (fun _ => rfl))
  intro _
  exact now

/-- The new-handshake timer uses the same exact queue acquisition as the
original source, after its endpoint reset. The intermediate native cut is kept. -/
theorem expiredNew_funded (pid : PeerId) {h : DurableHolders}
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((expiredNewHandshake pid).run w).run a = .ok (((),v),b)) :
    ∃ u middle delta,
      ((clearPeerEndpointSrc pid).run w).run a = .ok (((),u),middle) ∧
      ((sendQueuedHandshakeInitiation pid false).run u).run middle = .ok (((),v),b) ∧
      Handoff u v [] [] delta ∧ (h.absorb delta).Funded cs loans v ∧ StableRx cs v := by
  unfold expiredNewHandshake at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨x,u,middle,reset,queue⟩ := run
  cases x
  have kept := (hoare_iff_run_ambient _ _ _).mp (clearEndpoint_preserves pid)
    w a () u middle ⟨hi,stable⟩ reset
  obtain ⟨delta,step,funded,post⟩ := sendQueued_funded pid false kept.1 kept.2 middle b queue
  exact ⟨u,middle,delta,reset,queue,step,funded,post⟩

end Leanux.Proofs.WG.Queues.RxCredits.HolderTimers
