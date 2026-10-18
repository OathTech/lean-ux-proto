import Leanux.Proofs.WG.Queues.AdmissionOutcome
import Leanux.Proofs.WG.Queues.HolderNapi
import Leanux.Proofs.WG.Origins.HistoryAdapters

/-! A source-indexed relation over the unchanged RX journal. Admission steps
select their ledger using the actual native source receipt; poll steps subtract
only their own fresh removal suffix. This local relation does not yet cover the
runner, and a stopped admission has no stable-boundary transition here. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionPath
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open DurableHolders

def consume (msg : List UInt8) (src : SkbSource) (ds : Nat) : RxHistory.Obs Unit :=
  RxHistory.mixed (liftWGObserver (consumeDataPrefix msg src ds))

theorem consume_erases (msg src ds) :
    ErasesPrefix (consume msg src ds) (liftWG (consumeData msg src ds)) :=
  RxHistory.mixed_erases (liftWGObserver_erases (consumeDataPrefix_erases msg src ds))

theorem consume_appends (msg src ds) : Appends (consume msg src ds) :=
  Appends.focus _ _ _

/-- This is an actual source transition and a deterministic ledger change,
not a funding certificate. The old history may contain any events. -/
inductive Step : Ledger → World → List RxHistory.Event →
    Ledger → World → List RxHistory.Event → Prop
  | admission (run : runPrefix (consume msg src ds) w h = (.ok ((),v),k))
      (outcome : AdmissionOutcome.Outcome cs next msg src ds
        w.wg v.wg w.ambient v.ambient receipt) : Step cs w h next v k
  | poll (run : runPrefix (RxHistory.observePoll pid budget) w h = (.ok (count,v),k))
      (suffix : List RxHistory.Event) (history : k=h++suffix) :
      Step cs w h (remaining cs (NapiCarrier.removedPackets suffix)) v k

inductive Path : Ledger → World → List RxHistory.Event →
    Ledger → World → List RxHistory.Event → Prop
  | refl : Path cs w h cs w h
  | cons (step : Step cs w h middle u j) (tail : Path middle u j next v k) :
      Path cs w h next v k

theorem step_appends (step : Step cs w h next v k) : ∃ suffix, k=h++suffix := by
  cases step with
  | admission run outcome =>
    have ha := consume_appends
    rename_i msg src ds receipt
    obtain ⟨suffix,hs⟩ := ha msg src ds w h
    exact ⟨suffix,by simpa only [run] using hs⟩
  | poll run suffix history => exact ⟨suffix,history⟩

theorem path_appends (path : Path cs w h next v k) : ∃ suffix, k=h++suffix := by
  induction path with
  | refl => exact ⟨[],by simp⟩
  | cons step tail ih =>
    obtain ⟨a,ha⟩ := step_appends step
    obtain ⟨b,hb⟩ := ih
    exact ⟨a++b,by rw [hb,ha,List.append_assoc]⟩

theorem path_trans (first : Path cs w h middle u j) (second : Path middle u j next v k) :
    Path cs w h next v k := by
  induction first with
  | refl => exact second
  | cons step tail ih => exact .cons step (ih second)

/-- Every ordinary poll yields a source step, including the case with no
removals. The selected suffix is fixed by its actual incoming-history cut. -/
theorem poll_step (run : runPrefix (RxHistory.observePoll pid budget) w h = (.ok (count,v),k)) :
    ∃ next, Step cs w h next v k := by
  obtain ⟨suffix,hs⟩ := RxHistory.observePoll_appends pid budget w h
  exact ⟨_,.poll run suffix (by simpa only [run] using hs)⟩

theorem poll_ledger_unique (left : k=h++a) (right : k=h++b) :
    remaining cs (NapiCarrier.removedPackets a) = remaining cs (NapiCarrier.removedPackets b) := by
  have eq := List.append_cancel_left (left.symm.trans right)
  rw [eq]

theorem poll_boundary (run : runPrefix (RxHistory.observePoll pid budget) w h = (.ok (count,v),k))
    (history : k=h++suffix) (hi : Boundary cs loans w.wg) :
    Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg := by
  have post := (HolderNapi.observePoll_preserves cs loans h pid budget w h
    (HolderNapi.at_start hi h)).choose_spec.2.2
  rw [run] at post
  obtain ⟨actual,ha,boundary⟩ := post
  have same := List.append_cancel_left (ha.symm.trans history)
  simpa only [same] using boundary

/-- Accounting is derived separately. Admission needs the actual allocation
and physical-ring premises; polling itself already has a complete account rule. -/
theorem step_boundary (step : Step cs w h next v k) (hi : Boundary cs loans w.wg)
    (fresh : Packets.Inv w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) ringHistory w.wg) :
    Boundary next loans v.wg := by
  cases step with
  | admission run outcome => exact AdmissionOutcome.boundary hi fresh physical outcome
  | poll run suffix history => exact poll_boundary run history hi

/-- Extract the native cut from the original product observer. Full World and
Ambient endpoints are the ones returned by that same run. -/
theorem consume_native (run : runPrefix (consume msg src ds) w h = (.ok ((),v),k)) :
    ((consumeData msg src ds).run w.wg).run w.ambient=.ok (((),v.wg),v.ambient) :=
  DecryptIteration.native_normal (consume_erases msg src ds) run

/-- A supplied boundary and the concrete normal run establish a transition;
the next ledger is not assumed by the caller. -/
theorem admission_step (run : runPrefix (consume msg src ds) w h = (.ok ((),v),k))
    (hi : Boundary cs loans w.wg) (fresh : Packets.Inv w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) ringHistory w.wg) :
    ∃ next, Step cs w h next v k ∧ Boundary next loans v.wg := by
  obtain ⟨holders,funded,stable⟩ := hi
  obtain ⟨receipt,next,outcome,after,stableOut⟩ := AdmissionOutcome.consume funded stable fresh physical
    w.ambient v.ambient (consume_native run)
  exact ⟨next,.admission run outcome,holders,after,stableOut⟩

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionPath
