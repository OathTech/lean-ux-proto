import Leanux.Proofs.WG.Origins.HistoryAdapters
import Leanux.Proofs.WG.Queues.AdmissionOutcome

/-! An optional admission-receipt splice at the original consumeData cut.
The existing global ingress observers do not yet call this splice. Its
projection keeps the actual lifetime accesses and all stopped prefixes. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem consume_appends (msg src ds) : StateAppends (RxOrigin.consume msg src ds) := by
  unfold RxOrigin.consume RxOrigin.consumeWith RxOrigin.finishWith
    RxOrigin.observeAdmission RxOrigin.admitRaw RxOrigin.admitWith
  simp only [RxOrigin.allocate, liftWGPrefix, monadLift_self]
  repeat' first
    | with_reducible exact StateAppends.focus _ _ _
    | with_reducible exact StateAppends.lift _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply StateAppends.receiptWGObserved
    | with_reducible apply StateAppends.bind
    | (session_origin_intro_forall; try dsimp only)
    | split
  all_goals exact StateAppends.focus _ _ _

theorem front_appends (msg src ds) : StateAppends (RxOrigin.admitRaw msg src ds) := by
  unfold RxOrigin.admitRaw RxOrigin.admitWith
  simp only [RxOrigin.allocate, liftWGPrefix, monadLift_self]
  repeat' first
    | with_reducible exact StateAppends.focus _ _ _
    | with_reducible exact StateAppends.lift _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply StateAppends.receiptWGObserved
    | with_reducible apply StateAppends.bind
    | (session_origin_intro_forall; try dsimp only)
    | split
  all_goals exact StateAppends.focus _ _ _

theorem finish_appends (ctx) : StateAppends (finishObserved ctx) := by
  unfold finishObserved RxOrigin.finishWith
  simp only [liftWGPrefix, monadLift_self]
  repeat' first
    | with_reducible exact StateAppends.focus _ _ _
    | with_reducible exact StateAppends.lift _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply StateAppends.bind
    | (session_origin_intro_forall; try dsimp only)
    | split

def localConsume (msg : List UInt8) (src : SkbSource) (ds : Nat) : WGPrefix Origins.Event Unit :=
  focusStatePrefix Origins.rxEncode Origins.rxDecode (RxOrigin.consume msg src ds)

def observe (msg : List UInt8) (src : SkbSource) (ds : Nat) : RxHistory.Obs Unit :=
  Origins.HistoryAdapters.focus (liftWGObserver (localConsume msg src ds))

theorem local_projects (msg src ds) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) Origins.lifetime
      (localConsume msg src ds) (consumeDataPrefix msg src ds) := by
  intro w
  exact Origins.adapter_projects (I := fun h (_ : Ambient) => AllocationInv h w)
    Origins.rxEncode Origins.rxDecode (by intro e; cases e <;> rfl)
    (by intro e; cases e <;> rfl)
    ((RxOrigin.consume msg src ds).run w) ((consumeDataPrefix msg src ds).run w)
    (consume_appends msg src ds w) (RxOrigin.consume_projects msg src ds w)

theorem local_erases (msg src ds) :
    ErasesStatePrefix (localConsume msg src ds) (consumeData msg src ds) :=
  focusStatePrefix_erases _ _ (RxOrigin.consume_erases msg src ds)

theorem observe_appends (msg src ds) : Appends (observe msg src ds) :=
  Appends.focus _ _ _

theorem observe_erases (msg src ds) :
    ErasesPrefix (observe msg src ds) (liftWG (consumeData msg src ds)) :=
  focusPrefix_erases _ _ (liftWGObserver_erases (local_erases msg src ds))

theorem observe_projects (msg src ds) :
    ProjectsUnder AuditInv RxHistory.auditEvent (observe msg src ds)
      (auditFocus (liftWGObserver (consumeDataPrefix msg src ds))) := by
  apply Origins.HistoryAdapters.focus_projects _ _
    (StateAppends.focus _ _ _).liftWGObserver
  intro w h hi
  have projected := local_projects msg src ds w.wg w.ambient h hi
  change runWGPrefix (consumeDataPrefix msg src ds) w.wg w.ambient
      (h.filterMap Origins.lifetime) =
    ((runWGPrefix (localConsume msg src ds) w.wg w.ambient h).1,
      (runWGPrefix (localConsume msg src ds) w.wg w.ambient h).2.filterMap Origins.lifetime) at projected
  rw [liftWGObserver_run, liftWGObserver_run, projected]
  rfl

/-- The optional richer splice and the original global mixed cut agree on
the complete return (including Stop) and the audit history. Appends separately
retains every incoming RX/session/probe record; only new receipts are added. -/
theorem original_audit (msg src ds) (w : World) (h : List RxHistory.Event)
    (hi : AuditInv (RxHistory.auditHistory h) w) :
    ((runPrefix (observe msg src ds) w h).1,
      (runPrefix (observe msg src ds) w h).2.filterMap RxHistory.auditEvent) =
    ((runPrefix (RxHistory.mixed (liftWGObserver (consumeDataPrefix msg src ds))) w h).1,
      (runPrefix (RxHistory.mixed (liftWGObserver (consumeDataPrefix msg src ds))) w h).2.filterMap RxHistory.auditEvent) := by
  have left := observe_projects msg src ds w h hi
  have right := RxHistory.mixed_projects
    (consumeDataPrefix_allocation msg src ds).liftWGObserver w h hi
  exact left.symm.trans right

/-- The actual front receipt has a specified fresh occurrence even when its
finish stops. No equality-based membership search identifies the occurrence. -/
theorem native_receipt_at (r : WGRunWitness (Option RxOrigin.Admission))
    (hb : r.before=w) (ha : r.ambientBefore=ambient)
    (valid : r.Valid (RxOrigin.admitSource msg src ds)) (h) :
    ∃ front tail, (runWGPrefix (RxOrigin.consume msg src ds) w ambient h).2 =
      h ++ front ++ [.receipt (.admission msg src ds r)] ++ tail := by
  obtain ⟨front,hfront⟩ := front_appends msg src ds w ambient h
  change (runWGPrefix (RxOrigin.admitRaw msg src ds) w ambient h).2=h++front at hfront
  rw [consume_receipt r hb ha valid h]
  cases value:r.value with
  | none => exact ⟨front,[],by simp [hfront]⟩
  | some ctx =>
    obtain ⟨tail,htail⟩ := finish_appends ctx r.after r.ambientAfter
      ((runWGPrefix (RxOrigin.admitRaw msg src ds) w ambient h).2 ++
        [.receipt (.admission msg src ds r)])
    refine ⟨front,tail,htail.trans ?_⟩
    rw [hfront]

private theorem focus_occurrence {E F State α : Type}
    (encode : E → F) (decode : F → Option E) (g : PrefixT E State α)
    (w : State) (h : List F) (e : E)
    (present : ∃ front tail, (runPrefix g w (h.filterMap decode)).2 =
      h.filterMap decode ++ front ++ [e] ++ tail) :
    ∃ front tail, (runPrefix (focusPrefix encode decode g) w h).2 =
      h ++ front ++ [encode e] ++ tail := by
  obtain ⟨front,tail,history⟩ := present
  have equation : runPrefix g w (h.filterMap decode) =
      ((runPrefix g w (h.filterMap decode)).1,
        h.filterMap decode ++ (front ++ [e] ++ tail)) :=
    Prod.ext rfl (by simpa only [List.append_assoc] using history)
  rw [focusPrefix_suffix encode decode g w h _ _ equation]
  exact ⟨front.map encode,tail.map encode,by simp [List.map_append,List.append_assoc]⟩

/-- Both focuses retain the same native WG/Ambient witness and the fresh
receipt position. This covers later Stops without inventing a failed state. -/
theorem observe_receipt_at (r : WGRunWitness (Option RxOrigin.Admission))
    (hb : r.before=w.wg) (ha : r.ambientBefore=w.ambient)
    (valid : r.Valid (RxOrigin.admitSource msg src ds)) (h : List RxHistory.Event) :
    ∃ front tail, (runPrefix (observe msg src ds) w h).2 =
      h ++ front ++ [.rx (.admission msg src ds r)] ++ tail := by
  have lower := native_receipt_at r hb ha valid
    ((h.filterMap Origins.HistoryAdapters.decode).filterMap Origins.rxDecode)
  have focused := focus_occurrence Origins.rxEncode Origins.rxDecode
    ((RxOrigin.consume msg src ds).run w.wg) w.ambient
    (h.filterMap Origins.HistoryAdapters.decode) (.receipt (.admission msg src ds r)) lower
  exact focus_occurrence Origins.HistoryAdapters.encode Origins.HistoryAdapters.decode
    (liftWGObserver (localConsume msg src ds)) w h (.rx (.admission msg src ds r)) focused

/-- Exact whole-history splice: only the fresh native suffix is encoded.
Existing global receipts, probes and other event variants are retained. -/
theorem observe_suffix (msg src ds) (w : World) (h : List RxHistory.Event)
    (out : Except Stop ((Unit × WGWorld) × Ambient)) (suffix)
    (run : runWGPrefix (RxOrigin.consume msg src ds) w.wg w.ambient
      ((h.filterMap Origins.HistoryAdapters.decode).filterMap Origins.rxDecode) =
      (out, (h.filterMap Origins.HistoryAdapters.decode).filterMap Origins.rxDecode ++ suffix)) :
    runPrefix (observe msg src ds) w h =
      (out.map (fun ((x,wg),ambient) => (x,{w with wg,ambient})),
        h ++ suffix.map (fun e => Origins.HistoryAdapters.encode (Origins.rxEncode e))) := by
  have focused := focusPrefix_suffix Origins.rxEncode Origins.rxDecode
    ((RxOrigin.consume msg src ds).run w.wg) w.ambient
    (h.filterMap Origins.HistoryAdapters.decode) out suffix run
  have lifted : runPrefix (liftWGObserver (localConsume msg src ds)) w
      (h.filterMap Origins.HistoryAdapters.decode) =
      (out.map (fun ((x,wg),ambient) => (x,{w with wg,ambient})),
        h.filterMap Origins.HistoryAdapters.decode ++ suffix.map Origins.rxEncode) := by
    rw [liftWGObserver_run]
    change runWGPrefix (localConsume msg src ds) w.wg w.ambient
      (h.filterMap Origins.HistoryAdapters.decode) = _ at focused
    rw [focused]
  have global := focusPrefix_suffix Origins.HistoryAdapters.encode Origins.HistoryAdapters.decode
    (liftWGObserver (localConsume msg src ds)) w h _ (suffix.map Origins.rxEncode) lifted
  simpa only [observe,Origins.HistoryAdapters.focus,List.map_map,Function.comp_def] using global

/-- The original observer has exactly the same result and the lifetime
projection of that fresh suffix. The incoming history is copied unchanged,
rather than filtering away old receipts that happen to have equal values. -/
theorem original_suffix (msg src ds) (w : World) (h : List RxHistory.Event)
    (hi : AllocationInv (RxHistory.prior h) w.wg)
    (out : Except Stop ((Unit × WGWorld) × Ambient)) (suffix)
    (run : runWGPrefix (RxOrigin.consume msg src ds) w.wg w.ambient
      ((h.filterMap Origins.HistoryAdapters.decode).filterMap Origins.rxDecode) =
      (out, (h.filterMap Origins.HistoryAdapters.decode).filterMap Origins.rxDecode ++ suffix)) :
    runPrefix (RxHistory.mixed (liftWGObserver (consumeDataPrefix msg src ds))) w h =
      (out.map (fun ((x,wg),ambient) => (x,{w with wg,ambient})),
        h ++ (suffix.filterMap MaterialOrigin.life?).map (fun e => .audit (.lifetime e))) := by
  have input : (((h.filterMap Origins.HistoryAdapters.decode).filterMap Origins.rxDecode).filterMap
      MaterialOrigin.life?) = RxHistory.prior h := by
    rw [Origins.rx_lifetime,Origins.HistoryAdapters.input_lifetime]
  have projected := RxOrigin.consume_projects msg src ds w.wg w.ambient
    ((h.filterMap Origins.HistoryAdapters.decode).filterMap Origins.rxDecode) (input.symm ▸ hi)
  change runWGPrefix (consumeDataPrefix msg src ds) w.wg w.ambient _ =
    ((runWGPrefix (RxOrigin.consume msg src ds) w.wg w.ambient _).1,
      (runWGPrefix (RxOrigin.consume msg src ds) w.wg w.ambient _).2.filterMap MaterialOrigin.life?) at projected
  rw [run] at projected
  simp only [List.filterMap_append,input] at projected
  change ((runPrefix (liftWGObserver (consumeDataPrefix msg src ds)) w (RxHistory.prior h)).1,
      h ++ ((h.filterMap RxHistory.auditEvent ++
        ((runPrefix (liftWGObserver (consumeDataPrefix msg src ds)) w (RxHistory.prior h)).2.drop
          (RxHistory.prior h).length).map AuditEvent.lifetime).drop
            (h.filterMap RxHistory.auditEvent).length).map RxHistory.Event.audit) = _
  rw [liftWGObserver_run,projected]
  simp only [List.drop_left,List.map_map]
  rfl

/-- The same normal rich execution establishes both its fresh admission
occurrence and the source-selected complete account. No next ledger is supplied. -/
theorem normal (run : runPrefix (observe msg src ds) w h = (.ok ((),v),k))
    (hi : DurableHolders.Boundary cs loans w.wg) (fresh : Packets.Inv w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) ringHistory w.wg) :
    ∃ receipt next front tail,
      AdmissionOutcome.Outcome cs next msg src ds w.wg v.wg w.ambient v.ambient receipt ∧
      k=h++front++[.rx (.admission msg src ds receipt)]++tail ∧
      DurableHolders.Boundary next loans v.wg := by
  have native := DecryptIteration.native_normal (observe_erases msg src ds) run
  obtain ⟨holders,funded,stable⟩ := hi
  obtain ⟨receipt,next,outcome,after,stableOut⟩ := AdmissionOutcome.consume funded stable fresh physical
    w.ambient v.ambient native
  obtain ⟨front,tail,position⟩ := observe_receipt_at receipt outcome.1 outcome.2.1 outcome.2.2.1 h
  exact ⟨receipt,next,front,tail,outcome,by simpa only [run] using position,holders,after,stableOut⟩

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionJournal
