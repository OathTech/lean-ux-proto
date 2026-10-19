import Leanux.Proofs.WG.Queues.AdmissionReceive
import Leanux.Proofs.WG.Lifetimes.TrafficSource

/-! The unchanged receive callback shared by inject, flood and batch. Its
original journal remains authoritative; the dynamic ledger is selected from
the native execution at that same occurrence. Whole traffic-loop composition
and stopped-prefix transient accounting are separate obligations. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionCaller
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open DurableHolders

def receive (msg : List UInt8) (src : SkbSource) : RxHistory.Obs Unit :=
  RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))

theorem receive_erases (msg src) : ErasesPrefix (receive msg src) (liftWG (wgReceive msg src)) :=
  RxHistory.mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases msg src))

theorem receive_appends (msg src) : Appends (receive msg src) := Appends.focus _ _ _

/-- An exact normal occurrence in the original journal, with a source-derived
native ledger outcome. Funding is a consequence, not a field of the relation. -/
def Step (cs next : Ledger) (msg : List UInt8) (src : SkbSource)
    (w v : World) (h k : List RxHistory.Event) : Prop :=
  runPrefix (receive msg src) w h=(.ok ((),v),k) ∧
    AdmissionReceive.Outcome cs next msg src w.wg v.wg w.ambient v.ambient

theorem receive_step (hi : Boundary cs loans w.wg) (fresh : Packets.Inv w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) history w.wg)
    (run : runPrefix (receive msg src) w h=(.ok ((),v),k)) :
    ∃ next, Step cs next msg src w v h k ∧ Boundary next loans v.wg := by
  have actual := DecryptIteration.native_normal (receive_erases msg src) run
  obtain ⟨next,outcome,after⟩ := AdmissionReceive.normal hi fresh physical actual
  exact ⟨next,⟨run,outcome⟩,after⟩

theorem step_boundary (step : Step cs next msg src w v h k)
    (hi : Boundary cs loans w.wg) (fresh : Packets.Inv w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) history w.wg) : Boundary next loans v.wg := by
  obtain ⟨other,derived,after⟩ := receive_step hi fresh physical step.1
  exact (AdmissionReceive.Outcome.unique step.2 derived.2) ▸ after

theorem step_unique (left : Step cs next msg src w v h k)
    (right : Step cs other msg src w v h k) : next=other :=
  AdmissionReceive.Outcome.unique left.2 right.2

theorem step_appends (step : Step cs next msg src w v h k) : ∃ suffix, k=h++suffix := by
  obtain ⟨suffix,same⟩ := receive_appends msg src w h
  exact ⟨suffix,by simpa only [step.1] using same⟩

/-- These are literal specializations of the already shared caller sources.
They preserve all original guards, scheduler calls and stopped journals. -/
theorem inject_source (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    RxHistory.inject family port msg tos ll dest =
      TrafficSource.injectWith receive RxHistory.runCryptWorkers
        (fun what flags => RxHistory.mixed (requireDrainedPrefix what flags))
        family port msg tos ll dest := rfl

theorem flood_source (count port family : Nat) (messages : List (List UInt8)) :
    RxHistory.flood count port family messages =
      TrafficSource.floodWith receive RxHistory.pollScheduledInline RxHistory.afterBatch
        (fun what flags => RxHistory.mixed (requireDrainedPrefix what flags))
        count port family messages := rfl

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionCaller
