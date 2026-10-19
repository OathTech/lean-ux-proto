import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceDispatch
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalInitialized
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Initialized peer-reference positivity at the actual exchange entry worlds.
The same final source journal projects exactly, including stopped prefixes. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

theorem entry_initialized_safe {E : Type} [EntryFormat E]
    (trace : Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (EntrySource.execute (E := E) trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith (ProductInv (E := E)) (Safe (E := E))
    (fun _ _ hi => hi.1) product_wg_stable (Driver.syscallObserved (EntrySource.hooks (E := E)))
    syscall trace placeholders
  intro w same
  apply product_wg_stable [] {w with wg := initialWG trace.net trace.bare} w same
  exact ⟨safe_nil,initial trace.net trace.bare⟩

theorem initialized_safe (trace : Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 := by
  rw [← EntrySource.legacy_execute]
  exact entry_initialized_safe trace placeholders

theorem final_safe (trace : Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
      AuthenticatedEffects.CausalJournal.exchange?) := by
  have safe := initialized_safe trace placeholders
  rwa [ExchangeCausal.history_project] at safe

theorem final_entry (trace : Trace) (placeholders : Bool)
    (pre post : List AuthenticatedEffects.CausalJournal.Event) (event : Exchange.Event)
    (position : (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2 =
      pre ++ AuthenticatedEffects.CausalJournal.Event.exchange event :: post) :
    Inv event.before ∧ event.Valid := by
  have safe := final_safe trace placeholders
  apply safe event
  rw [position,List.filterMap_append,List.filterMap_cons]
  exact List.mem_append_right _ (by simp [AuthenticatedEffects.CausalJournal.exchange?])

theorem final_response_entry (trace : Trace) (placeholders : Bool)
    (pre post : List AuthenticatedEffects.CausalJournal.Event) (msg : Key)
    (r : WGRunWitness (Option PeerId))
    (position : (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2 =
      pre ++ AuthenticatedEffects.CausalJournal.Event.exchange (.consumeResponse msg r) :: post) :
    Inv r.before ∧ r.Valid (consumeResponse msg) :=
  final_entry trace placeholders pre post (.consumeResponse msg r) position

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
