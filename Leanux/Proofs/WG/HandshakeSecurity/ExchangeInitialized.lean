import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDispatch
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeOrigins
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Initialized native exchange history on the common driver. The remaining
premises are named per-call C2 H1 edge and tag facts; no invariant, reachability,
accepted-exchange history or authorization is supplied by the caller. Receipts
survive every later indexed Stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

theorem initialized_safe (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith ProductInv Safe
    (fun _ _ hi => hi.safe) product_wg_stable (Driver.syscallObserved ExchangeDriver.hooks)
    (syscall facts config traffic) trace placeholders
  intro w same
  apply product_wg_stable [] {w with wg := initialWG trace.net trace.bare} w same
  exact initial trace.net trace.bare

theorem initialized (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Trace) (placeholders : Bool) :
    History (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2
      (replay (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2) := by
  obtain ⟨ledger,history⟩ := initialized_safe facts config traffic trace placeholders
  rw [history.replayed]
  exact history

theorem initialized_response_once (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Trace) (placeholders : Bool)
    (pre between post : List Event) (first second : List UInt8)
    (r s : WGRunWitness (Option PeerId)) (pid : PeerId)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Event.consumeResponse first r :: between ++ Event.consumeResponse second s :: post)
    (accepted₁ : r.value = some pid) (accepted₂ : s.value = some pid) :
    ∃ epoch₁ epoch₂, ResponseAt pre pid epoch₁ ∧
      ResponseAt (pre ++ Event.consumeResponse first r :: between) pid epoch₂ ∧ epoch₁ < epoch₂ :=
  response_no_repeat (initialized facts config traffic trace placeholders)
    pre between post first second r s pid position accepted₁ accepted₂

theorem initialized_install_once (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Trace) (placeholders : Bool)
    (pre between post : List Event) (r s : WGRunWitness Bool) (pid : PeerId)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Event.session pid r :: between ++ Event.session pid s :: post)
    (accepted₁ : r.value = true) (accepted₂ : s.value = true) :
    ∃ epoch₁ epoch₂, InstallAt pre pid epoch₁ ∧
      InstallAt (pre ++ Event.session pid r :: between) pid epoch₂ ∧ epoch₁ < epoch₂ :=
  install_no_repeat (initialized facts config traffic trace placeholders)
    pre between post r s pid position accepted₁ accepted₂

theorem initialized_install_count (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Event.session pid r :: post) (success : r.value = true) :
    r.after.keypairCounter = r.before.keypairCounter + 1 ∧
    ∃ epoch, InstallAt pre pid epoch ∧ Origin pre pid epoch := by
  have history := initialized facts config traffic trace placeholders
  obtain ⟨epoch,binding⟩ := history.install_epoch pre post pid r position success
  exact ⟨installation_count facts.edges.session history pre post pid r position success,
    epoch,binding,history.install_origin pre post pid r position epoch binding⟩

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
