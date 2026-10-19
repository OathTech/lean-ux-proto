import Leanux.Proofs.WG.Queues.TxCompletionQueues

/-! Passive durable-holder fields through the actual TX step. Logical TX
queues and the send-work delta are accounted separately, not framed away. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem passive_from_frame {α : Type} (action : WG.M α)
    (frame : ∀ initial, Preserves (Frame initial) action) : SameView passiveView action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  exact ((hoare_iff_run_ambient _ _ _).mp (frame w) w a result v b (Frame.refl w) hr).passive

private theorem passive_modify (f : Device → Device)
    (base : ∀ d, (f d).peerList = d.peerList)
    (clear : ∀ d, (f d).clearWorkQueue = d.clearWorkQueue) (initial) :
    Preserves (fun w => passiveView w = initial) (modifyDev f) := by
  apply hoare_modify
  intro w hi
  simpa only [passiveView,Option.map_map,Function.comp_def,base,clear] using hi

macro "tx_passive_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a p v b hi hr
     simpa only [(getPeer_normal _ w v p a b hr).1] using hi)
  | (rx_retention_head setPeer; unfold setPeer)
  | (rx_retention_head modifyDev; apply passive_modify; intro d; rfl; intro d; rfl)
  | (rx_retention_head peerPut
     exact (passive_from_frame _ (HolderWorkFrames.peerPut_frame _)).wp (fun s => s = $initial))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

private theorem queued_passive (pid : PeerId) (retry : Bool) :
    SameView passiveView (sendQueuedHandshakeInitiation pid retry) := by
  intro initial
  change Preserves (fun w => passiveView w = initial) _
  unfold sendQueuedHandshakeInitiation peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,branch,branchCmp,
    unsupported,peekQueuedUnit,recordQueued]
  repeat' first
    | (rx_retention_head branchExpired
       exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => passiveView w = initial))
    | tx_passive_step initial

theorem createDataDone_passive (pid : PeerId) (item : List SkbId) :
    SameView passiveView (createDataDone pid item) := by
  rw [TxReservation.completion_factor]
  have lead := passive_from_frame _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.TxCompletionQueues.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.prefix_frame) pid item)
  apply lead.bind
  intro _ initial
  exact TxReservation.keepKeyFresh_preserves _ pid ((queued_passive pid false).wp (fun s => s = initial))

theorem txStep_passive (pid : PeerId) : SameView passiveView (txStep pid) := by
  intro initial
  change Preserves (fun w => passiveView w = initial) _
  unfold txStep WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head PrevQueue.peek
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a pair v b hi hr
       simpa only [(prev_peek_normal _ w v a b pair.1 pair.2 hr).2.2.2] using hi)
    | (rx_retention_head createDataDone
       exact (createDataDone_passive _ _).wp (fun s => s = initial))
    | (rx_retention_head getTxSkb
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a pkt v b hi hr
       simpa only [(Packets.getTxSkb_current _ w v pkt a b hr).1] using hi)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => passiveView w = initial)
       intro x b
       change Preserves (fun w => passiveView w = initial) _)
    | (rx_retention_head freeTxSkb
       unfold freeTxSkb
       apply hoare_liftSkb
       intro w d store hi hd
       simpa only [passiveView,hd,Option.map_some] using hi)
    | (rx_retention_head keypairPut
       exact (passive_from_frame _ (HolderWorkFrames.keypairPut_frame _ _)).wp (fun s => s = initial))
    | tx_passive_step initial

private theorem dead_body_send (pid : PeerId) (first : SkbId) (rest : List SkbId)
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient)
    (hr : ((TxDisposition.bodySource pid (some (first :: rest))).run w).run a =
      .ok ((result,v),b)) : sendView v = sendView w := by
  unfold TxDisposition.bodySource at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨go,checked,ac,hgo,hr⟩ := hr
  have hg : go = true ∧ checked = w := by
    change (((do
      let packet ← getTxSkb first
      branch .txNotUncrypted (packet.state != .uncrypted) : WG.M Bool).run w).run
        (CounterWindow.record a .txPacket true)) = .ok ((go,checked),ac) at hgo
    rw [MaterialOrigin.bind_ok_ambient] at hgo
    obtain ⟨pkt,readWorld,ar,hread,hbranch⟩ := hgo
    obtain ⟨readEq,dead⟩ :=
      (pinned_const _private.Leanux.Proofs.WG.Queues.DeadTxReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.dead_read)
        head _ _ hread
    subst readWorld
    simp only [dead] at hbranch
    cases hbranch
    exact ⟨rfl,rfl⟩
  obtain ⟨goEq,checkedEq⟩ := hg
  subst go
  subst checked
  simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,List.head?_cons,bind_assoc] at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨pkt,readWorld,ar,hread,hr⟩ := hr
  obtain ⟨readEq,dead⟩ :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.DeadTxReservation.«0».Leanux.Proofs.WG.Queues.RxCredits.TxReservation.dead_read)
      head ac ar hread
  subst readWorld
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨saved,s₁,a₁,h₁,hr⟩ := hr
  obtain ⟨s₁Eq,a₁Eq,d,hd,hp⟩ := getPeer_normal pid w s₁ saved ar a₁ h₁
  subst s₁
  subst a₁
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨current,s₂,a₂,h₂,hr⟩ := hr
  obtain ⟨s₂Eq,a₂Eq,d₂,hd₂,hp₂⟩ := getPeer_normal pid w s₂ current ar a₂ h₂
  subst s₂
  subst a₂
  have de : d₂ = d := Option.some.inj (hd₂.symm.trans hd)
  subst d₂
  have pe : current = saved := Option.some.inj (hp₂.symm.trans hp)
  subst current
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,dropped,ad,hdrop,hr⟩ := hr
  cases u
  have dropView : sendView dropped = sendView w := by
    cases hdrop
    simp only [sendView,hd,Option.map_some]
  simp only [dead] at hr
  change ((TxDisposition.disposeSource pid (first :: rest) pkt.keypair).run dropped).run
      (CounterWindow.record ad .txCrypted false) = .ok ((result,v),b) at hr
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (TxReservation.dispose_workQueues pid (first :: rest) pkt.keypair) dropped _ result v b hr
  have sendFrame : sendView v = sendView dropped := by
    simpa only [sendView,WorkQueueFrames.view,Option.map_map,Function.comp_def] using
      congrArg (Option.map fun q => q.2.1) frame
  exact sendFrame.trans dropView

theorem dead_step_send (o : Owner) (first : SkbId) (rest : List SkbId)
    (queue : ∃ p, RxCredits.resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) : sendView v = sendView w := by
  rw [← TxDisposition.stepSource_eq] at hr
  unfold TxDisposition.stepSource at hr
  simp only [bind_assoc] at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,read,ar,hread,hr⟩ := hr
  obtain ⟨readEq,arEq,d,hd,hp⟩ := getPeer_normal o.slot w read p a ar hread
  subst read
  subst ar
  obtain ⟨old,residentOld,hhead⟩ := queue
  obtain ⟨before,hbefore,_,hold,_⟩ := resident_fields residentOld
  have de : before = d := Option.some.inj (hbefore.symm.trans hd)
  subst before
  have pe : old = p := Option.some.inj (hold.symm.trans hp)
  subst old
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨⟨selected,q⟩,peeked,ap,hpeek,hr⟩ := hr
  obtain ⟨selectedEq,_,_,peekedEq⟩ := prev_peek_normal p.txQueue w peeked a ap selected q hpeek
  subst peeked
  have chosen : selected = some (first :: rest) := selectedEq.trans hhead
  rw [chosen] at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨current,read,ar,hread,hr⟩ := hr
  obtain ⟨readEq,arEq,d₂,hd₂,hp₂⟩ := getPeer_normal o.slot w read current ap ar hread
  subst read
  subst ar
  have de : d₂ = d := Option.some.inj (hd₂.symm.trans hd)
  subst d₂
  have pe : current = p := Option.some.inj (hp₂.symm.trans hp)
  subst current
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,installed,ai,hset,hr⟩ := hr
  cases u
  have installView : sendView installed = sendView w := by
    cases hset
    simp only [sendView,hd,Option.map_some]
  have nextHead : TxDisposition.HeadState first .dead installed := by
    cases hset
    simpa [TxDisposition.HeadState,TxDisposition.txPackets,setPeer,modifyDev,hd] using head
  exact (dead_body_send o.slot first rest nextHead ai b hr).trans installView


end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
