import Leanux.Proofs.WG.Index.ReceiveIngressCoreFrames
import Leanux.Proofs.WG.Index.DataIngressSource
import Leanux.Proofs.WG.Queues.AdmissionAuxiliary
import Leanux.Proofs.WG.Queues.BaseCoherenceTraffic

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReceiveIngressCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem packet_core
    (msg : List UInt8) (src : SkbSource) :
    Preserves Reached.Core (packetReceive msg src) := by
  rw [AdmissionReceive.packet_factor]
  apply preserves_bind (ConfigurationIndex.frame_core (packet_view_index_variant msg src))
  intro choice
  cases choice with
  | none => exact preserves_pure _
  | some ds => exact DataIngress.core msg src ds

theorem receive_core
    (msg : List UInt8) (src : SkbSource) :
    Preserves Reached.Core (wgReceive msg src) := by
  rw [AdmissionReceive.source_factor]
  apply preserves_bind (ConfigurationIndex.frame_core (front_view_index_variant msg src))
  intro choice
  cases choice with
  | none => exact preserves_pure _
  | some ds => exact DataIngress.core msg src ds

theorem packet_ready
    (msg : List UInt8) (src : SkbSource) :
    Preserves TimerCore.Ready (packetReceive msg src) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (CurrentSlots.packetReceive_preserves msg src)
    w a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp (packet_core msg src) w a result v b pre.2 run⟩

theorem receive_ready
    (msg : List UInt8) (src : SkbSource) :
    Preserves TimerCore.Ready (wgReceive msg src) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (CurrentSlots.wgReceive_preserves msg src)
    w a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp (receive_core msg src) w a result v b pre.2 run⟩

theorem receive_rebase
    {initial : Ledger} {loans : Reservations} {before h k : List RxHistory.Event}
    {w v : World} {msg : List UInt8} {src : SkbSource}
    (pre : Reached.Aux initial loans before h w)
    (run : runPrefix (AdmissionCaller.receive msg src) w h = (.ok ((),v),k)) :
    ∃ prior next, h=before++prior ∧
      AdmissionCaller.Step (remaining initial (NapiCarrier.removedPackets prior)) next msg src w v h k ∧
      Reached.Aux next loans k k v := by
  obtain ⟨prior,next,history,step,after⟩ := AdmissionAuxiliary.receive_rebase pre.1 run
  have native := DecryptIteration.native_normal (AdmissionCaller.receive_erases msg src) run
  have base := BaseCoherence.transport pre.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.wgReceive_view msg src)
      w.wg w.ambient () v.wg v.ambient native)
  have core := (hoare_iff_run_ambient _ _ _).mp (receive_core msg src)
    w.wg w.ambient () v.wg v.ambient pre.2.2 native
  exact ⟨prior,next,history,step,after,base,core⟩

theorem receive_any
    (loans : Reservations) (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (Reached.AnyAux loans) OwnerChecks.Safe (AdmissionCaller.receive msg src) := by
  intro w h pre
  obtain ⟨initial,entry⟩ := pre
  obtain ⟨suffix,history,safe,_⟩ := OwnerReceive.wgReceive_checked msg src w h entry.1.2.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (AdmissionCaller.receive msg src) w h).1 with
  | error e => trivial
  | ok out =>
    rcases out with ⟨⟨⟩,v⟩
    obtain ⟨prior,next,_,_,after⟩ := receive_rebase entry (Prod.ext run rfl)
    exact ⟨next,after⟩

end Leanux.Proofs.WG.Index.ReceiveIngressCore
