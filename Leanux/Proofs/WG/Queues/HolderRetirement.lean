import Leanux.Proofs.WG.Queues.HolderDrains
import Leanux.Proofs.WG.Queues.BaseRemoval

/-! Retirement retains its caller-owned stamped reservation through actual
work drains, then pays that occurrence exactly once. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem getPeer_keeps (P : WGWorld → Prop) (pid : PeerId) :
    Preserves P (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  exact (getPeer_normal pid w v p a b run).1 ▸ hi

private theorem getDev_keeps (P : WGWorld → Prop) : Preserves P getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a d v b hi run
  exact (DecryptCarrier.getDev_current a b run).1 ▸ hi

private theorem decrement_keeps : Preserves (DuringWork original cs loans)
    (modifyDev fun d => {d with numPeers := d.numPeers - 1}) := by
  apply hoare_modify
  intro w hi
  obtain ⟨holders,remainder,funded,stable⟩ := hi
  refine ⟨holders,remainder,⟨funded.aligned.frame ?_,funded.carriers.view ?_⟩,stable.view ?_⟩
  · constructor
    · simp only [passiveView,Option.map_map,Function.comp_def]
    · simp only [sendView,Option.map_map,Function.comp_def]
    · intro pid batches found
      simpa only [handoffTxView,Option.bind_map,Function.comp_def] using found
  · unfold carrierView keyView peerView rxView keyWords currentCells
    cases w.dev <;> rfl
  · unfold stableView RxRing.nativeCell rxView
    cases w.dev <;> rfl

private def beforePayment (pid : PeerId) : WG.M Unit :=
  getPeer pid >>= fun p =>
  branch .peerRemoveNotDead (!p.isDead) >>= fun notDead =>
  (if notDead then unsupported "peer_remove_after_dead: WARN_ON(!peer->is_dead)" else pure ()) >>= fun _ =>
  keypairsClear pid >>= fun _ =>
  timersStop pid >>= fun _ =>
  getDev >>= fun d =>
  (if !d.encryptQueue.empty || !d.decryptQueue.empty || !d.txWorkQueue.isEmpty
      || d.peers.toList.any (·.2.napiScheduled) then
    unsupported "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)" else pure ()) >>= fun _ =>
  drainHandshakeSendWq none >>= fun _ =>
  getDev >>= fun d =>
  (if d.numPeers == 0 then invariant "--num_peers below zero" else pure ()) >>= fun _ =>
  modifyDev fun d => {d with numPeers := d.numPeers - 1}

private theorem afterDead_factor (pid : PeerId) :
    peerRemoveAfterDead pid = (do beforePayment pid; peerPut (some pid)) := by
  simp only [peerRemoveAfterDead,beforePayment,bind_assoc,TxDisposition.bind_ite,pure_bind]

private theorem beforePayment_keeps (pid : PeerId) :
    Preserves (DuringWork original cs loans) (beforePayment pid) := by
  let P := DuringWork original cs loans
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  change Preserves P _
  unfold beforePayment
  apply preserves_bind (getPeer_keeps P pid)
  intro p
  apply preserves_bind (ambient (AmbientM.branch .peerRemoveNotDead (!p.isDead)))
  intro notDead
  apply preserves_bind
  · split
    · exact ambient (AmbientM.unsupported _)
    · exact preserves_pure ()
  · intro _
    apply preserves_bind (keypairsClear_preserves pid)
    intro _
    apply preserves_bind (timersStop_preserves pid)
    intro _
    apply preserves_bind (getDev_keeps P)
    intro d
    apply preserves_bind
    · split
      · exact ambient (AmbientM.unsupported _)
      · exact preserves_pure ()
    · intro _
      apply preserves_bind (drain_preserves none original cs loans)
      intro _
      apply preserves_bind (getDev_keeps P)
      intro d
      apply preserves_bind
      · split
        · exact ambient (AmbientM.invariant _)
        · exact preserves_pure ()
      · intro _
        exact decrement_keeps

/-- Pay one explicit transient occurrence, even when the same stamped owner
also appears in another charged holder. No final peer erasure is assumed. -/
theorem work_payment_normal (hi : DuringWork original cs (o :: loans) w)
    (a b : Ambient)
    (run : ((peerPut (some o.slot)).run w).run a = .ok (((),v),b)) :
    DuringWork original cs loans v := by
  obtain ⟨holders,remainder,funded,stable⟩ := hi
  have paid := reservation_payment_stable
    (WorkReservations.carrier_loans_perm funded.carriers List.perm_middle) stable a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderWorkFrames.peerPut_frame (some o.slot) w)
    w a () v b (Frame.refl w) run
  exact ⟨holders,remainder,⟨funded.aligned.frame frame,paid.1⟩,paid.2⟩

/-- The original after-dead source performs its real guards and both flushes
before paying only the supplied base reservation. Crypt-work Stops remain. -/
theorem afterDead_normal (hi : DuringWork original cs (o :: loans) w)
    (a b : Ambient)
    (run : ((peerRemoveAfterDead o.slot).run w).run a = .ok (((),v),b)) :
    DuringWork original cs loans v := by
  rw [afterDead_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,mid,c,prefixRun,payment⟩ := run
  cases u
  have kept := (hoare_iff_run_ambient _ _ _).mp (beforePayment_keeps o.slot)
    w a () mid c hi prefixRun
  exact work_payment_normal kept c b payment

theorem afterDead_observed_normal (hi : DuringWork original cs (o :: loans) w)
    (h : List LifetimeEvent) (a b : Ambient)
    (run : (runStatePrefix (peerRemoveAfterDeadPrefix o.slot) w a h).1 = .ok (((),v),b)) :
    DuringWork original cs loans v :=
  afterDead_normal hi a b ((peerRemoveAfterDeadPrefix_erases o.slot w a h).symm.trans run)

/-- The second original saved-list pass pays every saved occurrence in order.
Repeated equal slots remain separately charged; no distinctness is required. -/
theorem saved_afterDead_normal (saved : Reservations)
    (hi : DuringWork original cs (saved ++ loans) w) (a b : Ambient)
    (run : (((for pid in saved.map Owner.slot do
      _ ← branch .peerRemoveAllIter2 true
      peerRemoveAfterDead pid) : WG.M Unit).run w).run a = .ok (((),v),b)) :
    DuringWork original cs loans v := by
  induction saved generalizing w a with
  | nil =>
    simp only [List.map_nil,List.forIn_nil] at run
    cases run
    exact hi
  | cons o saved ih =>
    have factor : (for pid in (o :: saved).map Owner.slot do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead pid : WG.M Unit) = (do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead o.slot
        for pid in saved.map Owner.slot do
          _ ← branch .peerRemoveAllIter2 true
          peerRemoveAfterDead pid) := by
      simp only [List.map_cons,List.forIn_cons,bind_assoc,pure_bind]
    rw [factor,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨flag,read,c,decision,rest⟩ := run
    have same := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter2 true) (fun g => g=w))
      w a flag read c rfl decision
    subst read
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,paid,d,payment,rest⟩ := rest
    cases u
    exact ih (afterDead_normal hi c d payment) d rest

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
