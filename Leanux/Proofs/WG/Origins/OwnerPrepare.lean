import Leanux.Proofs.WG.Origins.OwnerControls
import Leanux.Proofs.WG.Origins.OwnerFocus

/-! The existing prepare observer certifies the actual decrypt entry before
publication. Later writes need only preserve its receipt journal; normal
carrier transport is supplied separately by the exact native source contract. -/
namespace Leanux.Proofs.WG.OwnerPrepare
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues
open Origins.HistorySupport (rxEncode rxDecode sensitive)

private def ReceiptChecked (r : RxOrigin.Receipt) : Prop :=
  OwnerChecks.Checked (rxEncode (.receipt r))

private theorem lift_carrier {α : Type} (a : WG.M α) (ha : Preserves OwnerBounds.Carrier a) :
    StatePrefixPreserves
      (fun h w _ => OwnerBounds.Carrier w ∧ MaterialOrigin.Valid ReceiptChecked h)
      (MaterialOrigin.Valid ReceiptChecked) (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ hi => hi.2)
    (fun _ w ambient x v finalAmbient hi hr =>
      ⟨(hoare_iff_run_ambient _ _ _).mp ha w ambient x v finalAmbient hi.1 hr,hi.2⟩)

private theorem decrypt_checks (id : SkbId) :
    StatePrefixEnsures
      (fun h w _ => OwnerBounds.Carrier w ∧ MaterialOrigin.Valid ReceiptChecked h)
      (MaterialOrigin.Valid ReceiptChecked) (RxOrigin.decrypt id)
      (fun _ h _ _ => MaterialOrigin.Valid ReceiptChecked h) := by
  intro w ambient h hi
  have base := (pinned_const _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.accessState_valid)
    (RxOrigin.readDecryptPrefix id) ReceiptChecked w ambient h hi.2
  obtain ⟨suffix,hs,hv,_⟩ := base
  change (runPrefix
    ((focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id)).run w)
    ambient h).2 = h ++ suffix at hs
  change MaterialOrigin.Valid ReceiptChecked (runPrefix
    ((focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id)).run w)
    ambient h).2 at hv
  have equation := runWGPrefix_receiptWGObserved
    (focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id))
    (MaterialOrigin.Event.receipt ∘ RxOrigin.Receipt.decrypt id) w ambient h
  change runWGPrefix (RxOrigin.decrypt id) w ambient h = _ at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : runPrefix
      ((focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life? (RxOrigin.readDecryptPrefix id)).run w)
      ambient h with
  | mk result journal =>
    simp only [run] at hs hv
    cases result with
    | error e => exact ⟨suffix,hs,hv,trivial⟩
    | ok out =>
      rcases out with ⟨⟨x,v⟩,finalAmbient⟩
      have final : MaterialOrigin.Valid ReceiptChecked
          (journal ++ [MaterialOrigin.Event.receipt (.decrypt id ⟨x,w,v,ambient,finalAmbient⟩)]) := by
        intro e member
        rcases List.mem_append.mp member with old | new
        · exact hv e old
        · obtain rfl := List.mem_singleton.mp new
          exact hi.1
      exact ⟨suffix ++ [MaterialOrigin.Event.receipt (.decrypt id ⟨x,w,v,ambient,finalAmbient⟩)],
        by simp only [hs,List.append_assoc,Function.comp_apply],final,final⟩

private theorem prepare_checks_native :
    StatePrefixEnsures
      (fun h w _ => OwnerBounds.Carrier w ∧ MaterialOrigin.Valid ReceiptChecked h)
      (MaterialOrigin.Valid ReceiptChecked) RxOrigin.prepare
      (fun _ h _ _ => MaterialOrigin.Valid ReceiptChecked h) := by
  unfold RxOrigin.prepare RxOrigin.prepareWith
  simp only [monadLift_self]
  apply StatePrefixEnsures.bind (lift_carrier getDev (OwnerControls.store _ getDev_sameWGStore))
  intro d
  cases queue : d.decryptQueue.consume with
  | mk item ring =>
    cases item with
    | none =>
      apply StatePrefixEnsures.bind (lift_carrier _ (hoare_liftAmbient (AmbientM.branch .decWorkerConsumed false) _))
      intro _
      exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi.2)
    | some id =>
      apply StatePrefixEnsures.bind (lift_carrier _ (hoare_liftAmbient (AmbientM.branch .decWorkerConsumed true) _))
      intro _
      apply StatePrefixEnsures.bind (lift_carrier _
        (OwnerControls.modifyDevice (fun d => { d with decryptQueue := ring }) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)))
      intro _
      apply StatePrefixEnsures.bind (decrypt_checks id)
      intro result
      rcases result with ⟨original,decrypted⟩
      simp only [liftWGPrefix]
      apply StatePrefixEnsures.bind ((pinned_const _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.validState_lift)
        ReceiptChecked (branch .decWorkerDecrypted decrypted.isSome : WG.M Bool))
      intro recorded
      split
      · cases decrypted with
        | none =>
          exact (pinned_const _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.validState_lift)
            ReceiptChecked (invariant "unreachable" : WG.M (Option PeerId))
        | some packet =>
          apply StatePrefixEnsures.bind ((pinned_const _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.accessState_valid)
            (setRxSkbPrefix id fun _ => packet) ReceiptChecked)
          intro _
          apply StatePrefixEnsures.bind ((pinned_const _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.accessState_valid)
            (RxWorkers.publishPrefix id .crypted) ReceiptChecked)
          intro pid
          exact (pinned_const _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.validState_pure)
            ReceiptChecked (some pid)
      · apply StatePrefixEnsures.bind ((pinned_const _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.accessState_valid)
          (RxWorkers.publishPrefix id .dead) ReceiptChecked)
        intro pid
        exact (pinned_const _private.Leanux.Proofs.WG.Packets.RxOriginCuts.«0».Leanux.Proofs.WG.RxOrigin.validState_pure)
          ReceiptChecked (some pid)

private theorem decoded_checked (e : RxHistory.Event) (r : RxOrigin.Receipt)
    (he : rxDecode e = some (.receipt r)) (hc : OwnerChecks.Checked e) : ReceiptChecked r := by
  cases e
  case audit event =>
    cases event <;> simp_all [rxDecode,Origins.HistoryAdapters.decode,Origins.rxDecode]
  case rx receipt =>
    change some (MaterialOrigin.Event.receipt receipt) = some (MaterialOrigin.Event.receipt r) at he
    cases he
    exact hc
  all_goals cases he

theorem prepare_checks (w : World) (h : List RxHistory.Event)
    (hi : OwnerChecks.Inv h w) :
    OwnerChecks.Checks (runPrefix Origins.HistoryAdapters.prepare w h).2 := by
  have initial : MaterialOrigin.Valid ReceiptChecked (h.filterMap rxDecode) := by
    intro entry member
    obtain ⟨e,sourceMember,decode⟩ := List.mem_filterMap.mp member
    cases entry with
    | life _ => trivial
    | receipt r => exact decoded_checked e r decode (hi.checked e sourceMember)
  have checked := (prepare_checks_native w.wg w.ambient (h.filterMap rxDecode)
    ⟨hi.carrier,initial⟩).choose_spec.2.1
  unfold Origins.HistoryAdapters.prepare Origins.HistoryAdapters.focus Origins.HistoryAdapters.localPrepare
  rw [Origins.HistorySupport.focus_compose]
  change OwnerChecks.Checks
    (h ++ ((runWGPrefix RxOrigin.prepare w.wg w.ambient (h.filterMap rxDecode)).2.drop
      (h.filterMap rxDecode).length).map rxEncode)
  apply hi.checked.append
  intro e member
  obtain ⟨entry,entry_member,rfl⟩ := List.mem_map.mp member
  have valid := checked entry (List.mem_of_mem_drop entry_member)
  cases entry with
  | life event => trivial
  | receipt r => exact valid

theorem prepare : OwnerChecks.Preserves Origins.HistoryAdapters.prepare := by
  apply OwnerChecks.combine _ CurrentWorkers.prepare Origins.HistoryAdapters.prepare_preserves
  · apply OwnerChecks.native_endpoint _ RxWorkers.prepareSource Origins.HistoryAdapters.prepare_erases
    intro history
    exact hoare_consequence OwnerDecrypt.prepareSource_preserves (fun _ hi => hi.2) (fun _ _ hi => hi)
  · exact prepare_checks

end Leanux.Proofs.WG.OwnerPrepare
